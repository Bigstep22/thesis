\subsubsection{Definition of Church encodings}
\begin{code}[hide]
open import agda.init.initial
module agda.church.defs where
\end{code}
This section defines Church encodings and the two conversions \tt{con} and \tt{abs}, called \tt{toCh} and \tt{fromCh} here, respectively.
It also defines the generalized producing, transformation, and consuming functions, as described by \cite{Harper2011}.
The church encoding, leveraging containers:
\begin{code}
data Church (F : Container 0ℓ 0ℓ) : Set₁ where
  Ch : ({X : Set} → (⟦ F ⟧ X → X) → X) → Church F
\end{code}
The conversion functions:
\begin{code}
toCh : {F : Container _ _} → μ F → Church F
toCh {F} x = Ch (λ {X : Set} → λ (a : ⟦ F ⟧ X → X) → ⦅ a ⦆ x)

fromCh : {F : Container _ _} → Church F → μ F
fromCh (Ch g) = g in'
\end{code}
The generalized and encoded producing, transformation, and consuming functions,
alongside proofs that they are equal to the functions they are encoding.
First the producing function, this is a generalized version of \cite{Gill1993}'s \tt{build} function:
\begin{code}
prodCh : {ℓ : Level}{F : Container _ _}{Y : Set ℓ}
         (g : {X : Set} → (⟦ F ⟧ X → X) → Y → X)(y : Y) → Church F
prodCh g x = Ch (λ a → g a x)

prod   : {ℓ : Level}{F : Container _ _}{Y : Set ℓ}
         (g : {X : Set} → (⟦ F ⟧ X → X) → Y → X)(y : Y) → μ F
prod g = fromCh ∘ prodCh g

eqProd : {F : Container _ _}{Y : Set}{g : {X : Set} → (⟦ F ⟧ X → X) → Y → X} →
         prod g ≡ g in'
eqProd = refl
\end{code}
Second, the natural transformation function:
\begin{code}
natTransCh : {F G : Container _ _}
             (nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) → Church F → Church G
natTransCh nat (Ch g) = Ch (λ a → g (a ∘ nat))

natTrans   : {F G : Container _ _}
             (nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) → μ F → μ G
natTrans nat = fromCh ∘ natTransCh nat ∘ toCh

eqNatTrans : {F G : Container _ _}
             {nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X} →
             natTrans nat ≡ ⦅ in' ∘ nat ⦆
eqNatTrans = refl
\end{code}
Third, the consuming function, note that this is a generalized version of \cite{Gill1993}'s \tt{foldr} function.
\begin{code}
consCh : {F : Container _ _}{X : Set}
         (c : ⟦ F ⟧ X → X) → Church F → X
consCh c (Ch g) = g c

cons   : {F : Container _ _}{X : Set}
         (c : ⟦ F ⟧ X → X) → μ F → X
cons c = consCh c ∘ toCh

eqCons : {F : Container _ _}{X : Set}{c : ⟦ F ⟧ X → X} →
         cons c ≡ ⦅ c ⦆
eqCons = refl
\end{code}
The below is left as an excercise to the reader:
\begin{code}
foldr : {F : Container _ _}{X : Set} → (⟦ F ⟧ X → X) → μ F → X
foldr c = consCh c ∘ toCh
build : {F : Container _ _}{X : Set} →
        ({Y : Set} → (⟦ F ⟧ Y → Y) → X → Y) →
        X → μ F
build g = fromCh ∘ prodCh g
--foldr-build-rule : {F : Container _ _}{X : Set} → (a : ⟦ F ⟧ X → X) →
--                   (g : {Y : Set} → (⟦ F ⟧ Y → Y) → X → Y) →
--                   foldr a ∘ build g ≡ g a
--foldr-build-rule a g =
\end{code}
