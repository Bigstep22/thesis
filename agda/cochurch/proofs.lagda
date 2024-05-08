\paragraph{Proof obligations} As with Church encodings, in \cite{Harper2011}'s work, five proof obligations needed to
be satisfied. These are formalized in this module.
\begin{code}[hide]
{-# OPTIONS --guardedness #-}
open import agda.term.termcoalg
open import agda.term.terminal
open import agda.term.cofusion
open import agda.funct.funext
open import agda.cochurch.defs
\end{code}
\begin{code}
module agda.cochurch.proofs where
\end{code}
The first proof proves that \tt{fromCoCh $\circ$ toCh = id}, using the reflection law:
\begin{code}
from-to-id : {F : Container 0ℓ 0ℓ} → fromCoCh ∘ toCoCh ≡ id
from-to-id {F} = funext (λ (x : ν F) → begin
    fromCoCh (toCoCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCoCh (CoCh out x)
  ≡⟨⟩ -- Definition of fromCh
    A⟦ out ⟧ x
  ≡⟨ reflection x ⟩
    x
  ≡⟨⟩
    id x
  ∎)
\end{code}
The second proof proof is similar to the first, but it proves the composition in the other direction
\tt{toCoCh $\circ$ fromCoCh = id}.
This proof leverages the parametricity as described by \cite{Wadler1989}.
It postulates the free theorem of the function g for a fixed Y \tt{f : $\forall$ X → (X → F X) → X → Y},
to prove that ``unfolding a Cochurch-encoded structure and then re-encoding it yields an equivalent structure'' \cite{Harper2011}:
\begin{code}
postulate free : {F : Container 0ℓ 0ℓ}
                 {C D : Set}{Y : Set₁}{c : C → ⟦ F ⟧ C}{d : D → ⟦ F ⟧ D}
                 (h : C → D)(f : {X : Set} → (X → ⟦ F ⟧ X) → X → Y) →
                 map h ∘ c ≡ d ∘ h → f c ≡ f d ∘ h
                 -- TODO: Do D and Y need to be the same thing? This may be a cop-out...
unfold-invariance : {F : Container 0ℓ 0ℓ}{Y : Set}
                    (c : Y → ⟦ F ⟧ Y) →
                    CoCh c ≡ (CoCh out) ∘ A⟦ c ⟧
unfold-invariance c = free A⟦ c ⟧ CoCh refl

to-from-id : {F : Container 0ℓ 0ℓ} → toCoCh ∘ fromCoCh {F} ≡ id
to-from-id = funext λ where
  (CoCh c x) → (begin
      toCoCh (fromCoCh (CoCh c x))
    ≡⟨⟩ -- definition of fromCh
      toCoCh (A⟦ c ⟧ x)
    ≡⟨⟩ -- definition of toCh
      CoCh out (A⟦ c ⟧ x)
    ≡⟨⟩ -- composition
      (CoCh out ∘ A⟦ c ⟧) x
    ≡⟨ cong (λ f → f x) (sym $ unfold-invariance c) ⟩
      CoCh c x
    ∎)
\end{code}
The third proof shows that cochurch-encoded functions constitute an implementation for the producing functions being replaced.
The proof is proved via reflexivity, but \cite{Harper2011}'s original proof steps are included here for completeness:
\begin{code}
prod-pres : {F : Container 0ℓ 0ℓ}{X : Set}(c : X → ⟦ F ⟧ X) →
            fromCoCh ∘ prodCoCh c ≡ A⟦ c ⟧
prod-pres c = funext λ x → begin
    fromCoCh ((λ s → CoCh c s) x)
  ≡⟨⟩ -- function application
    fromCoCh (CoCh c x)
  ≡⟨⟩ -- definition of toCh
    A⟦ c ⟧ x
  ∎
\end{code}
The fourth proof shows that cochurch-encoded functions constitute an implementation for the consuming functions being replaced.
The proof is proved via reflexivity, but \cite{Harper2011}'s original proof steps are included here for completeness:
\begin{code}
cons-pres : {F : Container 0ℓ 0ℓ}{X : Set} → (f : {Y : Set} → (Y → ⟦ F ⟧ Y) → Y → X) →
            consCoCh f ∘ toCoCh ≡ f out
cons-pres f = funext λ x → begin
    consCoCh f (toCoCh x)
  ≡⟨⟩ -- definition of toCoCh
    consCoCh f (CoCh out x)
  ≡⟨⟩ -- function application
    f out x
  ∎
\end{code}
The fifth, and final proof shows that cochurch-encoded functions constitute an implementation for the consuming functions being replaced.
The proof leverages the categorical fusion property and the naturality of \tt{f}:
\begin{code}
-- PAGE 52 - Proof 5
valid-hom : {F G : Container 0ℓ 0ℓ}{X : Set}(h : X → ⟦ F ⟧ X)
            (f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X)(nat : ∀ h → map h ∘ f ≡ f ∘ map h) →
            map A⟦ h ⟧ ∘ f ∘ h ≡ f ∘ out ∘ A⟦ h ⟧
valid-hom h f nat = begin
    (map A⟦ h ⟧ ∘ f) ∘ h
  ≡⟨ cong (λ f → f ∘ h) (nat A⟦ h ⟧) ⟩
    (f ∘ map A⟦ h ⟧) ∘ h
  ≡⟨⟩
    f ∘ out ∘ A⟦ h ⟧
  ∎

trans-pres : {F G : Container 0ℓ 0ℓ}{X : Set}(h : X → ⟦ F ⟧ X)
             (f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X)(nat : ∀ h → map h ∘ f ≡ f ∘ map h) →
             fromCoCh ∘ natTransCoCh f ∘ CoCh h ≡ A⟦ f ∘ out ⟧ ∘ A⟦ h ⟧
trans-pres h f nat = funext λ x → begin
    fromCoCh (natTransCoCh f (CoCh h x))
  ≡⟨⟩ -- Function application
    fromCoCh (CoCh (f ∘ h) x)
  ≡⟨⟩ -- Definition of fromCh
    A⟦ f ∘ h ⟧ x
  ≡⟨ cong (λ f → f x) $ fusion A⟦ h ⟧ (sym (valid-hom h f nat)) ⟩
    (A⟦ f ∘ out ⟧ ∘ A⟦ h ⟧) x
  ∎
\end{code}
Finally two additional proofs were made to clearly show that any pipeline made using cochurch
encodings will fuse down to a simple function application.
The first of these two proofs shows that any two composed natural transformation fuse down
to one single natural transformation:
\begin{code}
natfuse : {F G H : Container 0ℓ 0ℓ}
          (nat1 : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
          (nat2 : {X : Set} → ⟦ G ⟧ X → ⟦ H ⟧ X) →
          natTransCoCh nat2 ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh nat1 ≡ natTransCoCh (nat2 ∘ nat1)
natfuse nat1 nat2 = begin
            natTransCoCh nat2 ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh nat1
          ≡⟨ cong (λ f → natTransCoCh nat2 ∘ f ∘ natTransCoCh nat1) to-from-id ⟩
            natTransCoCh nat2 ∘ natTransCoCh nat1
          ≡⟨ funext (λ where (CoCh g s) → refl) ⟩
            natTransCoCh (nat2 ∘ nat1)
          ∎
\end{code}
The second of these two proofs shows that any pipeline, consisting of a producer, transformer,
and consumer function, fuse down to a single function application:
\begin{code}
pipefuse : {F G : Container 0ℓ 0ℓ}{X : Set}(c : X → ⟦ F ⟧ X)
           (nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
           (f : {Y : Set} → (Y → ⟦ G ⟧ Y) → Y → X) →
          cons f ∘ natTrans nat ∘ prod c ≡ f (nat ∘ c)
pipefuse c nat f = begin
    consCoCh f ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh nat ∘ toCoCh ∘ fromCoCh ∘ prodCoCh c
  ≡⟨ cong (λ g → consCoCh f ∘ g ∘ natTransCoCh nat ∘ toCoCh ∘ fromCoCh ∘ prodCoCh c) to-from-id ⟩
    consCoCh f ∘ natTransCoCh nat ∘ toCoCh ∘ fromCoCh ∘ prodCoCh c
  ≡⟨ cong (λ g → consCoCh f ∘ natTransCoCh nat ∘ g ∘ prodCoCh c) to-from-id ⟩
    consCoCh f ∘ natTransCoCh nat ∘ prodCoCh c
  ≡⟨⟩
    f (nat ∘ c)
  ∎
\end{code}
