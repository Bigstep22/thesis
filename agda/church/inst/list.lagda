\subsubsection{Example: List fusion}\label{sec:agda_church_list}
In order to clearly see how the Church encodings allows functions to fuse, a datatype was selected such that
the abstracted function, which have so far been used to prove the needed properties, can be instantiated
to demonstrate how the fusion works for functions across a cocrete datatype.
\begin{code}[hide]
open import Data.Product using (_×_)
open import Data.Nat.Base
open import Agda.Builtin.Nat
open import Data.Fin using (Fin; zero)
open import Data.Bool
open import agda.church.defs
open import agda.church.proofs
open import agda.church.initial
module agda.church.inst.list where
\end{code}
This section defines: the container, whose interpretation represents the base functor for lists,
some convenience functions to make type annotations more readable, a producer function \tt{between},
a transformation function \tt{map}, a consumer function \tt{sum}, and a proof that non-church and Church encoded
implementations are equal.

\subparagraph{Datatypes}
The index set for the container, as well as the container whose interpretation represents the base funtor for list.
Note how ListOp is isomorphic to the datatype \tt{$\top$ + const A}, I use ListOp instead to make the code more readable:
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
\subparagraph{Between}
The recursion principle \tt{b}, which when used, represents the between function.
It uses \tt{b'} to assist in termination checking:
\begin{code}
b' : {B : Set} → (a : List' ℕ B → B) → ℕ → ℕ → B
b' a x zero = a (nil , λ())
b' a x (suc n) = a (cons x , const (b' a (suc x)  n))
b : {B : Set} → (a : List' ℕ B → B) → ℕ × ℕ → B
b a (x , y) = b' a x (suc (y - x))
\end{code}
The functions \tt{between1} and \tt{between2}.
The former is defined without a Church encoding, the latter with.
A reflexive proof of equality and sanity check is included to show equality:
\begin{code}
between1 : ℕ × ℕ → List ℕ
between1 xy = b in' xy
between2 : ℕ × ℕ → List ℕ
between2 = build b
eqbetween : between1 ≡ between2
eqbetween = refl
checkbetween : 2 :: 3 :: 4 :: 5 :: 6 :: [] ≡ between2 (2 , 6)
checkbetween = refl
\end{code}
\subparagraph{Map}
The natural transformation \tt{m}, which when used in a transformation function, represents the map function:
\begin{code}
m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , _) = (nil , λ())
m f (cons n , l) = (cons (f n) , l)
\end{code}
The functions \tt{map1} and \tt{map2}.
The former is defined without a Church encoding, the latter with.
A reflexive proof of equality and sanity check is included to show equality:
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
\subparagraph{Sum}
The algebra \tt{s}, which when used in a consumer function, represents the sum function:
\begin{code}
s' : List' ℕ (ℕ → ℕ) → (ℕ → ℕ)
s' (nil , fn) s = s
s' (cons n , fn) s = fn zero (n + s)
s : List' ℕ ℕ → ℕ
s (nil , _) = 0
s (cons n , f) = n + f zero
\end{code}
The functions \tt{sum1} and \tt{sum2}.
The former is defined without a Church encoding, the latter with.
A reflexive proof of equality and sanity check is included to show equality:
\begin{code}
sum1 : List ℕ → ℕ
sum1 = ⦅ s ⦆
sum2 : List ℕ → ℕ
sum2 = foldr s
sum2' : List ℕ → ℕ
sum2' l = foldr s' l 0
checksum : sum2 (5 :: 6 :: 7 :: []) ≡ 18
checksum = refl


\end{code}
\subparagraph{Equality}
The below proof shows the equality between the non-Church endcoded pipeline and
the Church encoded pipeline:
\begin{code}
eq : {f : ℕ → ℕ}{x : ℕ × ℕ} → (sum1 ∘ map1 f ∘ between1) x ≡ (sum2 ∘ map2 f ∘ between2) x
eq {f}{x} = begin
    (⦅ s ⦆ ∘ ⦅ in' ∘ m f ⦆ ∘ b in') x
  ≡⟨ cong (⦅ s ⦆ ∘ ⦅ in' ∘ m f ⦆) (prod-pres b x) ⟩ -- refl
    (⦅ s ⦆ ∘ ⦅ in' ∘ m f ⦆ ∘ fromCh ∘ prodCh b) x
  ≡⟨ cong ⦅ s ⦆ (sym $ trans-pres (m f) (prodCh b x)) ⟩
    (⦅ s ⦆ ∘ fromCh ∘ natTransCh (m f) ∘ prodCh b) x
  ≡⟨ cons-pres s ((fromCh ∘ natTransCh (m f) ∘ prodCh b) x) ⟩ -- refl
    (consCh s ∘ toCh ∘ fromCh ∘ natTransCh (m f) ∘ prodCh b) x
  ≡⟨ cong (consCh s ∘ toCh ∘ fromCh ∘ natTransCh (m f))
          (sym $ to-from-id (prodCh b x)) ⟩
    (consCh s ∘ toCh ∘ fromCh ∘ natTransCh (m f) ∘ toCh ∘ fromCh ∘ prodCh b) x
  ≡⟨⟩
    (foldr s ∘ natTrans (m f) ∘ build b) x
  ∎
\end{code}
\paragraph{Fusing the functions down to a pipeline}
I present the equality between two functions: One is the \tt{pipeline} function and the other is the composition
of the three functions presented so far, along with the \tt{filter2} function.

The \tt{pipeline} function has been implemented with the aid of a \tt{pipeline'} function.
This is to aid in termination checking and the same technique used for \tt{b} and \tt{b'} above.

The \tt{filt'} function is a function that creates a new algebra from an existing one.
The \tt{filter2} function takes this partial algebra composition and encodes it using a build/foldr pair.
\begin{code}
filt' : {A X : Set} → (A → Bool) → (List' A X → X) → (List' A X → X)
filt' {A}{X} p f (nil , l) = f (nil , l)
filt' {A}{X} p f (cons a , l) = if (p a) then f (cons a , l) else l zero
filter2 : {A : Set} → (A → Bool) → List A → List A
filter2 {A} p = build (foldr ∘ filt' p)

pipeline' : (ℕ → Bool) → ℕ → ℕ → ℕ
pipeline' p x zero = zero
pipeline' p x (suc n) = if p x
                        then (1 + x) + pipeline' p (1 + x) n
                        else pipeline' p (1 + x) n
pipeline : (ℕ → Bool) → (ℕ × ℕ) → ℕ
pipeline p (x , y) = pipeline' p x (suc (y - x))
\end{code}
The \tt{eqPips} lemma proves that the fused pipelines are the same for all inputs using induction and pattern matching,
while the \tt{eqPipelines} lemma proves that the fusion is possible, even with this build/foldr pair.
One crucial insight for this latter proof is that \tt{prodCh} is associative for functions postcomposed to it.
This is stated formally in lemma \tt{prodAssoc} and proved via reflexivity.

These lemmas show, in as clear as a fashion as possible, that the composition of the Church encoded functions are equal
to the hand-fused pipeline written above.
\begin{code}
eqPips : (p : ℕ → Bool)(x y : ℕ) → b' (filt' p (s ∘ m (_+_ 1))) x y ≡ pipeline' p x y
eqPips p _ zero = refl
eqPips p zero (suc y) with p 0
... | true  = cong suc (eqPips p 1 y)
... | false = eqPips p 1 y
eqPips p (suc x) (suc y) with p (suc x)
... | true  = cong 2+ (cong (_+_ x) (eqPips p (2+ x) y))
... | false = eqPips p (2+ x) y

prodAssoc : {F : Container _ _}{Y : Set₁}{Z : Set}(g : {X : Set} → (⟦ F ⟧ X → X) → Y → X)(f : Z → Y)(z : Z) →
              (prodCh g ∘ f) z ≡ prodCh (λ a → g a ∘ f) z
prodAssoc _ _ _ = refl

eqPipelines : {p : ℕ → Bool}{xy : ℕ × ℕ} →
              (sum2 ∘ map2 (_+_ 1) ∘ filter2 p ∘ between2) xy ≡ pipeline p xy
eqPipelines {p}{xy@(x , y)} = begin
      (foldr s ∘ natTrans (m (_+_ 1)) ∘ fromCh ∘ prodCh (consCh ∘ filt' p) ∘ toCh ∘ fromCh ∘ prodCh b) xy
   ≡⟨ cong (foldr s ∘ natTrans (m (_+_ 1)) ∘ fromCh)
           (prodAssoc (consCh ∘ filt' p) (toCh ∘ fromCh ∘ prodCh b) xy) ⟩
      (foldr s ∘ natTrans (m (_+_ 1)) ∘ fromCh ∘ prodCh (λ a → consCh (filt' p a) ∘ toCh ∘ fromCh ∘ prodCh b)) xy
   ≡⟨ pipefuse (λ a → consCh (filt' p a) ∘ toCh ∘ fromCh ∘ prodCh b) (m (_+_ 1)) s xy ⟩
      (λ a → consCh (filt' p a) ∘ toCh ∘ fromCh ∘ prodCh b) (s ∘ m (_+_ 1)) xy
   ≡⟨⟩
      (consCh (filt' p (s ∘ m (_+_ 1))) ∘ toCh ∘ fromCh ∘ prodCh b) xy
   ≡⟨ cong (consCh (filt' p (s ∘ m (_+_ 1)))) (to-from-id (prodCh b xy)) ⟩
      (consCh (filt' p (s ∘ m (_+_ 1))) ∘ prodCh b)  xy
   ≡⟨⟩
      b (filt' p (s ∘ m (_+_ 1))) xy
   ≡⟨⟩
      b' (filt' p (s ∘ m (_+_ 1))) x (suc (y - x))
   ≡⟨ eqPips p x (suc (y - x)) ⟩
      pipeline' p x (suc (y - x))
    ≡⟨⟩
      pipeline p xy
    ∎
\end{code}
\begin{code}[hide]
-- Bonus functions
even : ℕ → Bool
even 0 = true
even (suc n) = not (even n)
odd : ℕ → Bool
odd 0 = false
odd (suc n) = not (odd n)
count : (ℕ → Bool) → μ (F ℕ) → ℕ
count p = ⦅ (λ where
               (nil , _) → 0
               (cons true , f) → 1 + f zero
               (cons false , f) → f zero) ⦆ ∘ map1 p
countworks : count even (5 :: 6 :: 7 :: 8 :: []) ≡ 2
countworks = refl
\end{code}
