\subsubsection{Proof obligations}
As with Church encodings, in \cite{Harper2011}'s work, five proof obligations needed to be satisfied.
These are formalized here.
\begin{code}[hide]
{-# OPTIONS --guardedness #-}
open import agda.term.terminal
open import agda.term.cofusion
open import agda.cochurch.defs
module agda.cochurch.proofs where
\end{code}
The first proof proves that \tt{fromCoCh $\circ$ toCh = id}, using the reflection law.
This corresponds to the first proof obligation mentioned in \autoref{sec:obligations}:
\begin{code}
from-to-id : {F : Container 0ℓ 0ℓ}(x : ν F) → (fromCoCh ∘ toCoCh) x ≡ id x
from-to-id {F} x = begin
    fromCoCh (toCoCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCoCh (CoCh out x)
  ≡⟨⟩ -- Definition of fromCh
    A⟦ out ⟧ x
  ≡⟨ reflection x ⟩
    x
  ≡⟨⟩ -- Definition of identity
    id x
  ∎
\end{code}
The second proof proof is similar to the first, but it proves the composition in the other direction
\tt{toCoCh $\circ$ fromCoCh = id}.
This proof leverages the parametricity as described by \cite{Wadler1989}.
It postulates the free theorem of the function g for a fixed Y: \tt{f :$\forall$ X → (X → F X) → X → Y},
to prove that ``unfolding a Cochurch-encoded structure and then re-encoding it yields an equivalent structure'' \citep{Harper2011}.
This together with the first proof shows that Cochurch encodings are isomorphic to the datatypes they are encoding:
\begin{code}
postulate free : {F : Container 0ℓ 0ℓ}
                 {C D : Set}{Y : Set₁}{c : C → ⟦ F ⟧ C}{d : D → ⟦ F ⟧ D}
                 (h : C → D)(f : {X : Set} → (X → ⟦ F ⟧ X) → X → Y) →
                 map h ∘ c ≡ d ∘ h → f c ≡ f d ∘ h
unfold-invariance : {F : Container 0ℓ 0ℓ}{Y : Set}
                    (c : Y → ⟦ F ⟧ Y) →
                    CoCh c ≡ CoCh out ∘ A⟦ c ⟧
unfold-invariance c = free A⟦ c ⟧ CoCh refl

to-from-id : {F : Container 0ℓ 0ℓ}(x : CoChurch F) → (toCoCh ∘ fromCoCh) x ≡ id x
to-from-id (CoCh c x) = begin
      toCoCh (fromCoCh (CoCh c x))
    ≡⟨⟩ -- definition of fromCh
      toCoCh (A⟦ c ⟧ x)
    ≡⟨⟩ -- definition of toCh
      CoCh out (A⟦ c ⟧ x)
    ≡⟨⟩ -- composition
      (CoCh out ∘ A⟦ c ⟧) x
    ≡⟨ cong (λ f → f x) (sym $ unfold-invariance c) ⟩
      CoCh c x
    ∎
\end{code}
The third proof shows that cochurch-encoded functions constitute an implementation for the producing functions being replaced.
The proof is proved via reflexivity, but \cite{Harper2011}'s original proof steps are included here for completeness.
This corresponds to the third proof obligation (second diagram) mentioned in \autoref{sec:obligations}:
\begin{code}
prod-pres : {F : Container 0ℓ 0ℓ}{X : Set}(c : X → ⟦ F ⟧ X) →
            (x : X) → (fromCoCh ∘ prodCoCh c) x ≡ A⟦ c ⟧ x
prod-pres c x = begin
    fromCoCh ((λ s → CoCh c s) x)
  ≡⟨⟩ -- function application
    fromCoCh (CoCh c x)
  ≡⟨⟩ -- definition of toCh
    A⟦ c ⟧ x
  ∎
\end{code}
The fourth proof shows that cochurch-encoded functions constitute an implementation for the consuming functions being replaced.
The proof is proved via reflexivity, but \cite{Harper2011}'s original proof steps are included here for completeness.
This corresponds to the fourth proof obligation (third diagram) mentioned in \autoref{sec:obligations}:
\begin{code}
cons-pres : {F : Container 0ℓ 0ℓ}{X : Set} → (f : {Y : Set} → (Y → ⟦ F ⟧ Y) → Y → X) →
            (x : ν F) → (consCoCh f ∘ toCoCh) x ≡ f out x
cons-pres f x = begin
    consCoCh f (toCoCh x)
  ≡⟨⟩ -- definition of toCoCh
    consCoCh f (CoCh out x)
  ≡⟨⟩ -- function application
    f out x
  ∎
\end{code}
The fifth, and final proof shows that cochurch-encoded functions constitute an implementation for the consuming functions being replaced.
The proof leverages the categorical fusion property and the naturality of \tt{f}.
This corresponds to the second proof obligation (first diagram) mentioned in \autoref{sec:obligations}:
\begin{code}
valid-hom : {F G : Container 0ℓ 0ℓ}{X : Set}(h : X → ⟦ F ⟧ X)
            (f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X)
            (nat : ∀ {X : Set}(g : X → ν F)(x : ⟦ F ⟧ X) → (map g ∘ f) x ≡ (f ∘ map g) x) →
            {x : X} → (map A⟦ h ⟧ ∘ f ∘ h) x ≡ (f ∘ out ∘ A⟦ h ⟧) x
valid-hom h f nat {x} = begin
    (map A⟦ h ⟧ ∘ f ∘ h) x
  ≡⟨ nat A⟦ h ⟧ (h x) ⟩
    (f ∘ map A⟦ h ⟧ ∘ h) x
  ≡⟨⟩ -- dfn of A⟦_⟧
    (f ∘ out ∘ A⟦ h ⟧) x
  ∎

trans-pres : {F G : Container 0ℓ 0ℓ}(f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X)
             (nat : {X : Set}(g : X → ν F)(x : ⟦ F ⟧ X) → (map g ∘ f) x ≡ (f ∘ map g) x)
             (x : CoChurch F) → (fromCoCh ∘ natTransCoCh f) x ≡ (A⟦ f ∘ out ⟧ ∘ fromCoCh) x
trans-pres f nat (CoCh h x) = begin
      fromCoCh (natTransCoCh f (CoCh h x))
    ≡⟨⟩ -- Function application
      fromCoCh (CoCh (f ∘ h) x)
    ≡⟨⟩ -- Definition of fromCh
      A⟦ f ∘ h ⟧ x
    ≡⟨ fusion A⟦ h ⟧ (sym $ valid-hom h f nat) x ⟩
      A⟦ f ∘ out ⟧ (A⟦ h ⟧ x)
    ≡⟨⟩ -- This step is not in the paper, but mirrors the one on the Church-side.
      A⟦ f ∘ out ⟧ (fromCoCh (CoCh h x))
    ∎
\end{code}
Finally two additional proofs were made to clearly show that any pipeline made using cochurch
encodings will fuse down to a simple function application.
The first of these two proofs shows that any two composed natural transformation fuse down
to one single natural transformation:
\begin{code}
natfuse : {F G H : Container 0ℓ 0ℓ}
          (nat1 : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
          (nat2 : {X : Set} → ⟦ G ⟧ X → ⟦ H ⟧ X)(x : CoChurch F) →
          (natTransCoCh nat2 ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh nat1) x ≡ natTransCoCh (nat2 ∘ nat1) x
natfuse nat1 nat2 x@(CoCh g s) = begin
            (natTransCoCh nat2 ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh nat1) x
          ≡⟨ cong (natTransCoCh nat2) (to-from-id (natTransCoCh nat1 x)) ⟩
            (natTransCoCh nat2 ∘ natTransCoCh nat1) x
          ≡⟨⟩
            natTransCoCh (nat2 ∘ nat1) x
          ∎
\end{code}
The second of these two proofs shows that any pipeline, consisting of a producer, transformer,
and consumer function, fuse down to a single function application:
\begin{code}
pipefuse : {F G : Container 0ℓ 0ℓ}{X : Set}(c : X → ⟦ F ⟧ X)
           (nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
           (f : {Y : Set} → (Y → ⟦ G ⟧ Y) → Y → X)(x : X) →
          (cons f ∘ natTrans nat ∘ prod c) x ≡ f (nat ∘ c) x
pipefuse c nat f x = begin
    (consCoCh f ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh nat ∘ toCoCh ∘ fromCoCh ∘ prodCoCh c) x
  ≡⟨ cong (consCoCh f ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh nat) (to-from-id (prodCoCh c x)) ⟩
    (consCoCh f ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh nat ∘ prodCoCh c) x
  ≡⟨ cong (consCoCh f) (to-from-id ((natTransCoCh nat ∘ prodCoCh c) x)) ⟩
    (consCoCh f ∘ natTransCoCh nat ∘ prodCoCh c) x
  ≡⟨⟩
    f (nat ∘ c) x
  ∎
\end{code}
