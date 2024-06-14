\begin{code}
open import Data.Sum as S
open import Data.Fin hiding (_+_; _>_; _-_)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Agda.Builtin.Nat
open import agda.church.defs
open import agda.church.proofs
open import agda.church.initial hiding (const)
\end{code}
\begin{code}
module agda.church.inst.free where
open import Data.Container.Combinator as C using (const; to-⊎; _⊎_)

--Below definition retrieved from Agda stdlib
Fr : Container 0ℓ 0ℓ → Set → Container 0ℓ 0ℓ
Fr f a = const a C.⊎ f

Free : Container 0ℓ 0ℓ → Set → Set
Free f a = μ (Fr f a)
Free' : Container 0ℓ 0ℓ → Set → Set → Set
Free' f a X = ⟦ Fr f a ⟧ X

record Handler (f f' : Container 0ℓ 0ℓ)(a b : Set) : Set where
  field
    hdlr : Free' f a (Free f' b) → Free f' b

-- Handle is a consumer! This might mean that we cannot fuse it! :(
handle : {f f' : Container _ _}{a b : Set} →
         (Free' f a (Free f' b) → Free f' b) →
         Free (f C.⊎ f') a → Free f' b
handle h = ⦅ (λ where
                (inj₁ a        , l) → h   (inj₁ a , l)
                (inj₂ (inj₁ x) , l) → h   (inj₂ x , l)
                (inj₂ (inj₂ y) , l) → in' (inj₂ y , l)) ⦆


\end{code}
