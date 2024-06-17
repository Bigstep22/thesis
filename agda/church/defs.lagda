\paragraph{Definition of Church encodings}
\begin{code}[hide]
open import agda.church.initial
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

build   : {ℓ : Level}{F : Container _ _}{Y : Set ℓ}
          (g : {X : Set} → (⟦ F ⟧ X → X) → Y → X)(y : Y) → μ F
build g = fromCh ∘ prodCh g

eqProd : {F : Container _ _}{Y : Set}{g : {X : Set} → (⟦ F ⟧ X → X) → Y → X} →
         build g ≡ g in'
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

foldr   : {F : Container _ _}{X : Set}
         (c : ⟦ F ⟧ X → X) → μ F → X
foldr c = consCh c ∘ toCh

eqCons : {F : Container _ _}{X : Set}{c : ⟦ F ⟧ X → X} →
         foldr c ≡ ⦅ c ⦆
eqCons = refl
\end{code}
