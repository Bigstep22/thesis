\paragraph{Proof obligations}
In \cite{Harper2011}'s work, five proofs proofs are given for Church encodings.
These are formalized in this module.
\begin{code}[hide]
open import Data.Container using (Container; μ; ⟦_⟧; map)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Function.Base using (id; _∘_)
open import agda.init.initalg
open import agda.init.initial
open import agda.funct.funext
open import agda.church.defs
open import Data.Product using (_,_)
\end{code}
\begin{code}
module agda.church.proofs where
open import Data.W using () renaming (sup to in')
\end{code}
The first proof proves that \tt{fromCh $\circ$ toCh = id}, using the reflection law:
\begin{code}
from-to-id : {F : Container 0ℓ 0ℓ} → fromCh ∘ toCh ≡ id
from-to-id {F} = funext (λ (x : μ F) → begin
    fromCh (toCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCh (Ch (λ {X : Set} → λ (a : ⟦ F ⟧ X → X) → ⦅ a ⦆ x))
  ≡⟨⟩ -- Definition of fromCh
    (λ a → ⦅ a ⦆ x) in'
  ≡⟨⟩ -- function application
    ⦅ in' ⦆ x
  ≡⟨ reflection x ⟩
    x
  ∎)
\end{code}
The second proof is similar to the first, but it proves the composition in the other direction \tt{toCh $\circ$ fromCh = id}.
This proofs leverages parametricity as described by \cite{Wadler1989}.
It postulates the free theorem of the function \tt{g : $forall$ A . (F A -> A) -> A},
to prove that ``applying \tt{g} to \tt{b} and then passing the result to \tt{h},
is the same as just folding \tt{c} over the datatype'' \citep{Harper2011}:
\begin{code}
postulate free : {F : Container 0ℓ 0ℓ}{B C : Set}{b : ⟦ F ⟧ B → B} {c : ⟦ F ⟧ C → C}
                 (h : B → C)(g : {X : Set} → (⟦ F ⟧ X → X) → X) →
                 h ∘ b ≡ c ∘ map h → h (g b) ≡ g c
fold-invariance : {F : Container 0ℓ 0ℓ}{Y : Set}
                  (g : {X : Set} → (⟦ F ⟧ X → X) → X)(a : ⟦ F ⟧ Y → Y) →
                  ⦅ a ⦆ (g in') ≡ g a
fold-invariance g a = free ⦅ a ⦆ g refl

to-from-id : {F : Container 0ℓ 0ℓ} → toCh ∘ fromCh {F} ≡ id
to-from-id {F} = funext (λ where
  (Ch g) → begin
      toCh (fromCh (Ch g))
    ≡⟨⟩ -- definition of fromCh
      toCh (g in')
    ≡⟨⟩ -- definition of toCh
      Ch (λ{X}a → ⦅ a ⦆ (g in'))
    ≡⟨ cong Ch (funexti λ{Y} → funext (fold-invariance g)) ⟩
      Ch g
    ∎)
\end{code}
The third proof shows church-encoded functions constitute an implementation for the consumer functions being replaced.
The proof is proved via reflexivity, but \cite{Harper2011}'s original proof steps are included here for completeness:
\begin{code}
cons-pres : {F : Container 0ℓ 0ℓ}{X : Set}(b : ⟦ F ⟧ X → X) →
            consCh b ∘ toCh ≡ ⦅ b ⦆
cons-pres {F} b = funext λ (x : μ F) → begin
    consCh b (toCh x)
  ≡⟨⟩ -- definition of toCh
    consCh b (Ch (λ a → ⦅ a ⦆ x))
  ≡⟨⟩ -- function application
    (λ a → ⦅ a ⦆ x) b
  ≡⟨⟩ -- function application
    ⦅ b ⦆ x
  ∎
\end{code}
The fourth proof shows that church-encoded functions constitute an implementation for the producing functions being replaced.
The proof is proved via reflexivity, but \cite{Harper2011}'s original proof steps are included here for completeness:
\begin{code}
prod-pres : {F : Container 0ℓ 0ℓ}{X : Set}(f : {Y : Set} → (⟦ F ⟧ Y → Y) → X → Y) →
            fromCh ∘ prodCh f ≡ f in'
prod-pres {F}{X} f = funext λ (s : X) → begin
    fromCh ((λ (x : X) → Ch (λ a → f a x)) s)
  ≡⟨⟩ -- function application
    fromCh (Ch (λ a → f a s))
  ≡⟨⟩ -- definition of fromCh
    (λ {Y : Set} (a : ⟦ F ⟧ Y → Y) → f a s) in'
  ≡⟨⟩ -- function application
    f in' s
  ∎
\end{code}
The fifth, and final proof shows that church-encoded functions constitute an implementation for the conversion functions being replaced.
The proof again leverages the free theorem defined earlier:
\begin{code}
trans-pres : {F G : Container 0ℓ 0ℓ} (f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
             fromCh ∘ natTransCh f ≡ ⦅ in' ∘ f ⦆ ∘ fromCh
trans-pres f = funext (λ where
  (Ch g) → (begin
      fromCh (natTransCh f (Ch g))
    ≡⟨⟩ -- Function application
      fromCh (Ch (λ a → g (a ∘ f)))
    ≡⟨⟩ -- Definition of fromCh
      (λ a → g (a ∘ f)) in'
    ≡⟨⟩ -- Function application
      g (in' ∘ f)
    ≡⟨ sym (fold-invariance g (in' ∘ f)) ⟩
      ⦅ in' ∘ f ⦆ (g in')
    ≡⟨⟩ -- Definition of fromCh
      ⦅ in' ∘ f ⦆ (fromCh (Ch g))
    ∎))
\end{code}
Finally two additional proofs were made to clearly show that any pipeline made using church
encodings will fuse down to a simple function application.
The first of these two proofs shows that any two composed natural transformation fuse down
to one single natural transformation:
\begin{code}
natfuse : {F G H : Container 0ℓ 0ℓ}
          (nat1 : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
          (nat2 : {X : Set} → ⟦ G ⟧ X → ⟦ H ⟧ X) →
          natTransCh nat2 ∘ toCh ∘ fromCh ∘ natTransCh nat1 ≡ natTransCh (nat2 ∘ nat1)
natfuse nat1 nat2 = begin
            natTransCh nat2 ∘ toCh ∘ fromCh ∘ natTransCh nat1
          ≡⟨ cong (λ f → natTransCh nat2 ∘ f ∘ natTransCh nat1) to-from-id ⟩
            natTransCh nat2 ∘ natTransCh nat1
          ≡⟨ funext (λ where (Ch g) → refl) ⟩
            natTransCh (nat2 ∘ nat1)
          ∎
\end{code}
The second of these two proofs shows that any pipeline, consisting of a producer, transformer,
and consumer function, fuse down to a single function application:
\begin{code}
pipefuse : {F G : Container 0ℓ 0ℓ}{X : Set}(g : {Y : Set} → (⟦ F ⟧ Y → Y) → X → Y)
          (nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X)(c : (⟦ G ⟧ X → X)) →
          cons c ∘ natTrans nat ∘ prod g ≡ g (c ∘ nat)
pipefuse g nat c = begin
    consCh c ∘ toCh ∘ fromCh ∘ natTransCh nat ∘ toCh ∘ fromCh ∘ prodCh g
  ≡⟨ cong (λ f → consCh c ∘ f ∘ natTransCh nat ∘ toCh ∘ fromCh ∘ prodCh g) to-from-id ⟩
    consCh c ∘ natTransCh nat ∘ toCh ∘ fromCh ∘ prodCh g
  ≡⟨ cong (λ f → consCh c ∘ natTransCh nat ∘ f ∘ prodCh g) to-from-id ⟩
    consCh c ∘ natTransCh nat ∘ prodCh g
  ≡⟨⟩
    g (c ∘ nat)
  ∎
\end{code}
