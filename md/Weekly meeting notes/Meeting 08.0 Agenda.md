# First-stage review meeting

Postulates:
- $\nu$Ext
- Fusion (cata- and ana-)
- Funext (for implicit and explicit functions)
- Free theorems (for the initial and terminal parametric functions)
- Valid-hom (in cochurch proof nr.5)
	- Will likely require definitions of natural transformations and proof of coherence property.
Termination-check disable:
- Initial.agda (only for the proof of the reflection law)
- Terminal.agda (proof of reflection and _definition of ana-_...)
	- Termination check for ana- needs to be fixed.
Guardedness for all proof and definitions involving coinduction (e.g. anamorphisms and cochurch definitions and proof).


## How does this fit into the big picture?
In functional languages it is important to have code run performantly.
This can be achieved in a number of ways, one of which is fusion.
When one has a pipeline of functions, it is possible to fuse them into one single function, reducing computational overhead and allowing the compiler to apply further optimizations.
In Harper's paper, 'A Library Writer's Guide to Shortcut Fusion', the process for implementing fusion through Church and CoChurch encoding is described.
When implemented the code is faster, but the implementation process can be a little unwieldy and employs 'trust me' pragmas to ensure that Haskell cooperates.
My project:
- Aims to formally verify the proofs:
	- By implementing them safely in Agda relying on only well-known postulates, such as functional extensionality.
- Aims to tie the proofs back to the code that ends up being written:
	- By implementing a system that can (hopefully) auto-generate this fusable code, reducing the space for errors to be made by people wanting this optimization.

## How does church-encoded fusion work?
Say we want the chain of the following functions as one:
```haskell
sum . map (+1) . filter odd . between
```

I will present the _idea_ behind Church encodings:
```haskell
data List_ a b = Nil_ | NilT_ b | Cons_ a b deriving Functor
data List a = Nil | Cons a (List a) deriving (Functor, Show)
data ListCh a = ListCh (forall b . (List_ a b -> b) -> b)

toCh :: List a -> ListCh a
toCh t = ListCh (\a -> fold a t)
fold :: (List_ a b -> b) -> List a -> b
fold a Nil = a Nil_
fold a (Cons x xs) = a (Cons_ x (fold a xs))

fromCh :: ListCh a -> List a
fromCh (ListCh fold) = fold in'
in' :: List_ a (List a) -> List a
in' Nil_ = Nil
in' (NilT_ b) = b
in' (Cons_ x xs) = Cons x xs
```
Focus on the toCh and fromCh.
- toCh takes an input datastructure and puts it into a thunked fold that is still waiting for an input function
- fromCh takes the fold, and executes it, replacing our Tree_ datastructure with the normal Tree.
Church encoded versions of sum, map (+1), filter odd, and between look like the following:
```haskell
s :: List_ Int Int -> Int
s Nil_ = 0
s (NilT_ x) = x
s (Cons_ x y) = x + y
sumCh :: ListCh Int -> Int
sumCh (ListCh g) = g s

m :: (a -> b) -> List_ a c -> List_ b c
m f Nil_ = Nil_
m f (NilT_ xs) = NilT_ xs
m f (Cons_ x xs) = Cons_ (f x) xs
mapCh :: (a -> b) -> ListCh a -> ListCh b
mapCh f (ListCh g) = ListCh (\a -> g (a . m f))

filt :: (a -> Bool) -> List_ a c -> List_ a c
filt p Nil_ = Nil_
filt p (NilT_ xs) = NilT_ xs
filt p (Cons_ x xs) = if p x then Cons_ x xs else NilT_ xs
filterCh :: (a -> Bool) -> ListCh a -> ListCh a
filterCh p (ListCh g) = ListCh (\a -> g (a . filt p))

b :: (Int, Int) -> (List_ Int b -> b) -> b
b (x, y) a
| x > y = a Nil_
| x <= y = a (Cons_ x (b a (x+1,y)))
betweenCh :: (Int, Int) -> ListCh Int
betweenCh (x, y) = ListCh (\a -> b a (x, y))
```
Next, the _actual_ functions:
```haskell
sum :: List Int -> Int
sum = sumCh . toCh

map :: (a -> b) -> List a -> List b
map f = fromCh . mapCh f . toCh

filter :: (a -> Bool) -> List a -> List a
filter p = fromCh . filterCh p . toCh

between :: (Int, Int) -> List Int
between = fromCh . betweenCh
```
Remember the pipeline? Now it looks like this:
```haskell
f = sum . map (+1) . filter odd . between

f =	     sumCh .        toCh .
fromCh . mapCh (+1) .   toCh .
fromCh . filterCh odd . toCh .
fromCh . betweenCh
```
When 'fused' it looks like this:
```haskell
sumCh . mapCh (+1) . filterCh odd . betweenCh
```
For some input (x, y):
```haskell
sumCh . mapCh (+1) . filterCh odd . betweenCh (x, y)
sumCh . mapCh (+1) . filterCh odd . TreeCh (\a -> b a (x, y))
-- Dfn of betweenCh
sumCh . mapCh (+1) . TreeCh (\a' -> (\a -> b a (x, y)) (a' . filt odd))
-- Substitution
sumCh . mapCh (+1) . TreeCh (\a' -> b (a' . filt odd) (x, y))
-- Dfn of map
sumCh . TreeCh (\a -> (\a' -> b (a' . filt odd)(x, y)) (a . m (+1)))
-- Substitution
sumCh . TreeCh (\a -> b (a . m (+1) . filt odd) (x, y))
-- Dfn of sumCh
(\a -> b ((a . m (+1)) . filt odd) (x, y)) s
-- Substitution
f' = b (s . m (+1) . filt odd) (x, y)
-- Dfn of b, replace above expression with f'
| x > y = (s . m (+1) . filt odd) Nil_
| x <= y = (s . m (+1) . filt odd) (Cons_ x (f' (x+1, y)))
-- Dfn of filt 
| x > y = (s . m (+1)) Nil_
| x <= y = if odd x
            then (s . m (+1)) (Cons_ x (f' (x+1, y)))
            else (s . m (+1)) (NilT_ (f' (x+1, y)))
-- Dfn of m
| x > y = s Nil_
| x <= y = if odd x
            then s (Cons_ (x+1) (f' (x+1, y)))
            else s (NilT_ (f' (x+1, y)))
-- Dfn of s
| x > y = 0
| x <= y = if odd x
            then (x+1) + (f' (x+1, y))
            else f' (x+1, y)
```
$\blacksquare$
This is how the fusion for church encodings work.
CoChurch encodings seem to work slightly differently, in that they express this recursion in terms of an unfold instead of direct recursion.