\paragraph{Definition of Church encodings}
\begin{code}[hide]
open import Data.Container using (Container; μ; ⟦_⟧)
open import Level using (0ℓ)
open import agda.init.initalg
open import Function
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
\end{code}
This module defines church encodings and the two conversions \tt{con} and \tt{abs}, called \tt{toCh} and \tt{fromCh} here, respectively.
It also defines the generalized producing, transformation, and consuming functions, as described by \cite{Harper2011}.
\begin{code}
module agda.church.defs where
open import Data.W using () renaming (sup to in')
\end{code}
The church encoding, leveraging containers:
\begin{code}
data Church (F : Container 0ℓ 0ℓ) : Set₁ where
  Ch : ({X : Set} → (⟦ F ⟧ X → X) → X) → Church F
\end{code}
The conversion functions:
\begin{code}
toCh : {F : Container _ _} → μ F → Church F
toCh {F} x = Ch (λ {X : Set} → λ (a : ⟦ F ⟧ X → X) → ⦅ a ⦆ x)
fromCh : {F : Container 0ℓ 0ℓ} → Church F → μ F
fromCh (Ch g) = g in'
\end{code}
The generalized encoded producing, transformation, and consuming function,
alongside proofs that they are equal to the functions they are encoding:
\begin{code}
-- Generalized producer and consuming functions.
prodCh : {F : Container _ _}{X : Set}(g : {Y : Set} → (⟦ F ⟧ Y → Y) → X → Y)(x : X) → Church F
prodCh g x = Ch (λ a → g a x)
eqprod : {F : Container _ _}{X : Set}{g : {Y : Set} → (⟦ F ⟧ Y → Y) → X → Y} →
         fromCh ∘ prodCh g ≡ g in'
eqprod = refl
transCh : {F G : Container _ _}(nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) → Church F → Church G
transCh n (Ch g) = Ch (λ a → g (a ∘ n))
eqtrans : {F G : Container _ _}{nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X} →
          fromCh ∘ transCh nat ∘ toCh ≡ ⦅ in' ∘ nat ⦆
eqtrans = refl
consCh : {F : Container _ _}{X : Set} → (c : (⟦ F ⟧ X → X)) → Church F → X
consCh c (Ch g) = g c
eqcons : {F : Container _ _}{X : Set}{c : (⟦ F ⟧ X → X)} →
         consCh c ∘ toCh ≡ ⦅ c ⦆
eqcons = refl
\end{code}
