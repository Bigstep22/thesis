\subsubsection{Proof obligations}
In \cite{Harper2011}'s work, five proofs are given for Church encodings.
These are formalized here.
\begin{code}[hide]
open import agda.church.initial
open import agda.funct.funext
open import agda.church.defs
module agda.church.proofs where
\end{code}
The first proof shows that \tt{fromCh $\circ$ toCh = id}, using the reflection law.
This corresponds to the first proof obligation mentioned in \autoref{sec:obligations}:
\begin{code}
from-to-id : {F : Container 0ℓ 0ℓ}(x : μ F) →
             (fromCh ∘ toCh) x ≡ id x
from-to-id x = begin
    fromCh (toCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCh (Ch (λ {X}a → ⦅ a ⦆ x))
  ≡⟨⟩ -- Definition of fromCh
    (λ a → ⦅ a ⦆ x) in'
  ≡⟨⟩ -- function application
    ⦅ in' ⦆ x
  ≡⟨ reflection ⟩
    x
  ∎
\end{code}
The second proof is similar to the first, but it proves the composition in the other direction \tt{toCh $\circ$ fromCh = id}.
This proofs leverages parametricity as described by \cite{Wadler1989}.
It postulates the free theorem of the function \tt{g :$\forall$ A . (F A -> A) -> A},
to prove that ``applying \tt{g} to \tt{b} and then passing the result to \tt{h},
is the same as just folding \tt{c} over the datatype'' \citep{Harper2011}.
This together with the first proof shows that Church encodings are isomorphic to the datatypes they are encoding:
\begin{code}
postulate free : {F : Container 0ℓ 0ℓ}{B C : Set}{b : ⟦ F ⟧ B → B} {c : ⟦ F ⟧ C → C}
                 (h : B → C)(g : {X : Set} → (⟦ F ⟧ X → X) → X) →
                 h ∘ b ≡ c ∘ map h → h (g b) ≡ g c
fold-invariance : {F : Container 0ℓ 0ℓ}{Y : Set}
                  (g : {X : Set} → (⟦ F ⟧ X → X) → X)(a : ⟦ F ⟧ Y → Y) →
                  ⦅ a ⦆ (g in') ≡ g a
fold-invariance g a = free ⦅ a ⦆ g refl

to-from-id : {F : Container 0ℓ 0ℓ}(x : Church F) →
             (toCh ∘ fromCh) x ≡ id x
to-from-id (Ch g) = begin
      toCh (fromCh (Ch g))
    ≡⟨⟩ -- definition of fromCh
      toCh (g in')
    ≡⟨⟩ -- definition of toCh
      Ch (λ{X}a → ⦅ a ⦆ (g in'))
    ≡⟨ cong Ch (funexti λ{Y} → funext (fold-invariance g)) ⟩
      Ch g
    ∎
\end{code}
The third proof shows Church encoded functions constitute an implementation for the consumer functions being replaced.
The proof is proved via reflexivity, but \cite{Harper2011}'s original proof steps are included here for completeness.
This corresponds to the third proof obligation (second diagram) mentioned in \autoref{sec:obligations}:
\begin{code}
cons-pres : {F : Container 0ℓ 0ℓ}{X : Set}(b : ⟦ F ⟧ X → X) →
            (x : μ F) → (consCh b ∘ toCh) x ≡ ⦅ b ⦆ x
cons-pres b x = begin
    consCh b (toCh x)
  ≡⟨⟩ -- definition of toCh
    consCh b (Ch (λ a → ⦅ a ⦆ x))
  ≡⟨⟩ -- function application
    (λ a → ⦅ a ⦆ x) b
  ≡⟨⟩ -- function application
    ⦅ b ⦆ x
  ∎
\end{code}
The fourth proof shows that Church encoded functions constitute an implementation for the producing functions being replaced.
The proof is proved via reflexivity, but \cite{Harper2011}'s original proof steps are included here for completeness.
This corresponds to the fourth proof obligation (third diagram) mentioned in \autoref{sec:obligations}:
\begin{code}
prod-pres : {F : Container 0ℓ 0ℓ}{X : Set}(f : {Y : Set} → (⟦ F ⟧ Y → Y) → X → Y) →
            (s : X) → (fromCh ∘ prodCh f) s ≡ f in' s
prod-pres {F}{X} f s = begin
    fromCh ((λ (x : X) → Ch (λ a → f a x)) s)
  ≡⟨⟩ -- function application
    fromCh (Ch (λ a → f a s))
  ≡⟨⟩ -- definition of fromCh
    (λ {Y : Set} (a : ⟦ F ⟧ Y → Y) → f a s) in'
  ≡⟨⟩ -- function application
    f in' s
  ∎
\end{code}
The fifth, and final proof shows that Church encoded functions constitute an implementation for the conversion functions being replaced.
The proof again leverages the free theorem defined earlier.
This corresponds to the second proof obligation (first diagram) mentioned in \autoref{sec:obligations}:
\begin{code}
trans-pres : {F G : Container 0ℓ 0ℓ}(f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
             (x : Church F) → (fromCh ∘ natTransCh f) x ≡ (⦅ in' ∘ f ⦆ ∘ fromCh) x
trans-pres f (Ch g) = begin
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
    ∎
\end{code}
Finally, two additional proofs were made to clearly show that any pipeline made using church
encodings will fuse down to a simple function application.
The first of these two proofs shows that any two composed natural transformation fuse down
to one single natural transformation:
\begin{code}
natfuse : {F G H : Container 0ℓ 0ℓ}
          (nat1 : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
          (nat2 : {X : Set} → ⟦ G ⟧ X → ⟦ H ⟧ X) → (x : Church F) →
          (natTransCh nat2 ∘ toCh ∘ fromCh ∘ natTransCh nat1) x ≡ natTransCh (nat2 ∘ nat1) x
natfuse {F}{G}{H} nat1 nat2 x@(Ch g) = begin
            (natTransCh nat2 ∘ toCh ∘ fromCh ∘ natTransCh nat1) x
          ≡⟨ cong (natTransCh nat2) (to-from-id (natTransCh nat1 x)) ⟩
            (natTransCh nat2 ∘ natTransCh nat1) x
          ≡⟨ refl ⟩
            natTransCh (nat2 ∘ nat1) x
          ∎
\end{code}
The second of these two proofs shows that any pipeline, consisting of a producer, transformer,
and consumer function, fuse down to a single function application:
\begin{code}
pipefuse : {F G : Container 0ℓ 0ℓ}{X : Set}(g : {Y : Set} → (⟦ F ⟧ Y → Y) → X → Y)
          (nat : {Y : Set} → ⟦ F ⟧ Y → ⟦ G ⟧ Y)(c : (⟦ G ⟧ X → X)) →
          (x : X) → (foldr c ∘ natTrans nat ∘ build g) x ≡ g (c ∘ nat) x
pipefuse {F}{G} g nat c x = begin
    (consCh c ∘ toCh ∘ fromCh ∘ natTransCh nat ∘ toCh ∘ fromCh ∘ prodCh g) x
  ≡⟨ cong (consCh c ∘ toCh ∘ fromCh ∘ natTransCh nat) (to-from-id (prodCh g x)) ⟩
     (consCh c ∘ toCh ∘ fromCh ∘ natTransCh nat ∘ prodCh g) x
  ≡⟨ cong (consCh c) (to-from-id (natTransCh nat (prodCh g x))) ⟩
    (consCh c ∘ natTransCh nat ∘ prodCh g) x
  ≡⟨⟩
    g (c ∘ nat) x
  ∎
\end{code}
