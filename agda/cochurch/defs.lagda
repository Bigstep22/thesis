\paragraph{Definition of Cochurch encodings}
This module defines Cochurch encodings and the two conversion functions \tt{con} and \tt{abs}, called \tt{toCoCh} and \tt{fromCoCh} here, respectively.
It also defines the generalized producing, transformation, and consuming functions, as described by \cite{Harper2011}.
The definition of the CoChurch datatypes is defined slightly differently to how it is initially defined by \cite{Harper2011}.
Instead an Isomorphic definition is used, whose type is described later on on the same page.
The original definition is included as \tt{CoChurch'}.
\begin{code}
{-# OPTIONS --guardedness #-}
module agda.cochurch.defs where
\end{code}
\begin{code}[hide]
open import Data.Container using (Container; ⟦_⟧)
open import agda.term.termcoalg
open ν
open import agda.funct.funext
open import Data.Product
open import Level
open import Function
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
\end{code}
The Cochurch encoding, agian leveraging containers:
\begin{code}
data CoChurch (F : Container 0ℓ 0ℓ) : Set₁ where
  CoCh : {X : Set} → (X → ⟦ F ⟧ X) → X → CoChurch F
\end{code}
The conversion functions:
\begin{code}
toCoCh : {F : Container 0ℓ 0ℓ} → ν F → CoChurch F
toCoCh x = CoCh out x
fromCoCh : {F : Container 0ℓ 0ℓ} → CoChurch F → ν F
fromCoCh (CoCh h x) = A⟦ h ⟧ x
\end{code}
The generalized encoded producing, transformation, and consuming functions, alongside the proof that they are equal to the functions they are encoding.
First, the producing function, note that this is a generalized version of \cite{Svenningsson2002}'s \tt{unfoldr} function:
\begin{code}
prodCoCh : {F : Container 0ℓ 0ℓ}{Y : Set} → (g : Y → ⟦ F ⟧ Y) → Y → CoChurch F
prodCoCh g x = CoCh g x
eqprod : {F : Container 0ℓ 0ℓ}{Y : Set}{g : (Y → ⟦ F ⟧ Y)} →
         fromCoCh ∘ prodCoCh g ≡ A⟦ g ⟧
eqprod = refl
\end{code}
Second the transformation function:
\begin{code}
transCoCh : {F G : Container 0ℓ 0ℓ}(nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) → CoChurch F → CoChurch G
transCoCh n (CoCh h s) = CoCh (n ∘ h) s
eqtrans : {F G : Container 0ℓ 0ℓ}{nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X} →
          fromCoCh ∘ transCoCh nat ∘ toCoCh ≡ A⟦ nat ∘ out ⟧
eqtrans = refl
\end{code}
Third the consuming function, note that this a is a generalized version of \cite{Svenningsson2002}'s \tt{destroy} function:
\begin{code}
consCoCh : {F : Container 0ℓ 0ℓ}{Y : Set} → (c : {S : Set} → (S → ⟦ F ⟧ S) → S → Y) → CoChurch F → Y
consCoCh c (CoCh h s) = c h s
eqcons : {F : Container 0ℓ 0ℓ}{X : Set}{c : {S : Set} → (S → ⟦ F ⟧ S) → S → X} →
         consCoCh c ∘ toCoCh ≡ c out
eqcons = refl
\end{code}
The original CoChurch definition is included here for completeness' sake, but it is note used elsewhere in the code.
\begin{code}
data CoChurch' (F : Container 0ℓ 0ℓ) : Set₁ where
  cochurch : (∃ λ S → (S → ⟦ F ⟧ S) × S) → CoChurch' F
\end{code}
A mapping from \tt{CoChurch'} to \tt{CoChurch} and back is provided as well as a proof that their compositions are equal to the identity function, thereby proving isomorphism:
\begin{code}
toConv : {F : Container _ _} → CoChurch' F → CoChurch F
toConv (cochurch (S , (h , x))) = CoCh {_}{S} h x
fromConv : {F : Container _ _} → CoChurch F → CoChurch' F
fromConv (CoCh {X} h x) = cochurch ((X , h , x))
to-from-conv-id : {F : Container 0ℓ 0ℓ} → toConv ∘ fromConv {F} ≡ id
to-from-conv-id = funext λ where
    (CoCh {X} h x) → refl
from-to-conv-id : {F : Container 0ℓ 0ℓ} → fromConv ∘ toConv {F} ≡ id
from-to-conv-id = funext λ where
    (cochurch (S , (h , x))) → refl
\end{code}
