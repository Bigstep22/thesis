\paragraph{Proof obligations}
In \cite{Harper2011l}'s work, five proofs proofs are given for Church encodings.
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
The second proof is similar to the first, but it proves the composition in theo ther direction \tt{toCh $\circ$ fromCh = id}.
This proofs leverages parametricity as described by \cite{Wadler1989}.
It postulates the free theorem of the function \tt{g}, to prove that ``applying \tt{g} to \tt{b} and then passing
the result to \tt{h} is the same as just folding \tt{c} over the datatype'' \citep{Harper2011}:
\begin{code}
postulate freetheorem-initial : {F : Container 0ℓ 0ℓ}{B C : Set}{b : ⟦ F ⟧ B → B}{c : ⟦ F ⟧ C → C}
                                (h : B → C)(g : {X : Set} → (⟦ F ⟧ X → X) → X) →
                                h ∘ b ≡ c ∘ map h → h (g b) ≡ g c
fold-invariance : {F : Container 0ℓ 0ℓ}{Y : Set}
                  (g : {X : Set} → (⟦ F ⟧ X → X) → X)(a : ⟦ F ⟧ Y → Y) →
                  ⦅ a ⦆ (g in') ≡ g a
fold-invariance g a = freetheorem-initial ⦅ a ⦆ g refl
to-from-id : {F : Container 0ℓ 0ℓ}{g : {X : Set} → (⟦ F ⟧ X → X) → X} →
             toCh (fromCh (Ch g)) ≡ Ch g
to-from-id {F}{g} = begin
    toCh (fromCh (Ch g))
  ≡⟨⟩ -- definition of fromCh
    toCh (g in')
  ≡⟨⟩ -- definition of toCh
    Ch (λ{X}a → ⦅ a ⦆ (g in'))
  ≡⟨ cong Ch (funexti λ{Y} → funext (fold-invariance g)) ⟩
    Ch g
  ∎
to-from-id' : {F : Container 0ℓ 0ℓ} → toCh ∘ fromCh ≡ id
to-from-id' {F} = funext (λ where (Ch g) → to-from-id {F}{g})
\end{code}
The third proof shows that encoding functions constitute an implementation for the consumer functions being replaced:
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
The fourth proof shows that producing functions constitute an implementation for the producing functions being replaced:
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
The fifth, and final proof proof shows that conversion functions constitute an implementation for the conversion functions being replaced:
\begin{code}
-- This last proofs could all use a rewrite, now that I've generalized the three different types of functions...
chTrans : {F G : Container 0ℓ 0ℓ}(f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) → Church F → Church G
chTrans f (Ch g) = Ch (λ a → g (a ∘ f))
trans-pred : {F G : Container 0ℓ 0ℓ}(g : {X : Set} → (⟦ F ⟧ X → X) → X )
             (f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
             fromCh (chTrans f (Ch g)) ≡ ⦅ in' ∘ f ⦆ (fromCh (Ch g))
trans-pred g f = begin
    fromCh (chTrans f (Ch g))
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
  ∎
\end{code}
