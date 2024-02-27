I will present the _idea_ behind Church encodings:
```haskell
data List_ a b = Nil_ | Cons_ a b deriving Functor
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
in' (Cons_ x xs) = Cons x xs
```
Focus on the toCh and fromCh.
- toCh takes an input datastructure and puts it into a thunked fold that is still waiting for an input function
- fromCh takes the fold, and executes it, replacing our Tree_ datastructure with the normal Tree.
Church encoded versions of sum, map (+1), filter odd, and between look like the following:
```haskell
s :: List_ Int Int -> Int
s Nil_ = 0
s (Cons_ x y) = x + y
sumCh :: ListCh Int -> Int
sumCh (ListCh g) = g s

m :: (a -> b) -> List_ a c -> List_ b c
m f Nil_ = Nil_
m f (Cons_ x xs) = Cons_ (f x) xs
mapCh :: (a -> b) -> ListCh a -> ListCh b
mapCh f (ListCh g) = ListCh (\a -> g (a . m f))

filterCh :: (a -> Bool) -> ListCh a -> ListCh a
filterCh p (ListCh g) = ListCh (\a -> g (\case
   Nil_ -> a Nil_
   Cons_ x xs -> if (p x) then a (Cons_ x xs) else xs
 ))

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

f =	     sumCh        . toCh .
fromCh . mapCh (+1)   . toCh .
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
-- Dfn of betweenCh
sumCh . mapCh (+1) . filterCh odd . ListCh (\a -> b a (x, y))
-- Dfn of filterCh
sumCh . mapCh (+1) . ListCh (\a' -> (\a -> b a (x, y)) (\case
   Nil_ -> a' Nil_
   Cons_ x xs -> if (p x) then a' (Cons_ x xs) else xs
 ))
-- Substitution
sumCh . mapCh (+1) . ListCh (\a' -> b (\case
   Nil_ -> a' Nil_
   Cons_ x xs -> if (p x) then a' (Cons_ x xs) else xs
 ) (x, y))
-- Dfn of mapCh
sumCh . ListCh (\a -> (\a' -> b (\case
   Nil_ -> a' Nil_
   Cons_ x xs -> if (p x) then a' (Cons_ x xs) else xs
 ) (x, y)) (a . m (+1)))
-- Substitution
sumCh . ListCh (\a -> b (\case
   Nil_ -> (a . m (+1)) Nil_
   Cons_ x xs -> if (p x) then (a . m (+1)) (Cons_ x xs) else xs
 ) (x, y))
-- Dfn of sumCh
(\a -> b (\case
   Nil_ -> (a . m (+1)) Nil_
   Cons_ x xs -> if (p x) then (a . m (+1)) (Cons_ x xs) else xs
 ) (x, y)) s
-- Substitution
b (\case
   Nil_ -> (s . m (+1)) Nil_
   Cons_ x xs -> if (p x) then (s . m (+1)) (Cons_ x xs) else xs
) (x, y))

f' = b (\case
   Nil_ -> (s . m (+1)) Nil_
   Cons_ x xs -> if (p x) then (s . m (+1)) (Cons_ x xs) else xs)
-- Dfn of b, substituting f'
| x > y = (\case
   Nil_ -> (s . m (+1)) Nil_
   Cons_ x xs -> if (p x) then (s . m (+1)) (Cons_ x xs) else xs
) Nil_
| x <= y = (\case
   Nil_ -> (s . m (+1)) Nil_
   Cons_ x xs -> if (p x) then (s . m (+1)) (Cons_ x xs) else xs
) (Cons_ x (f' (x+1, y)))
-- Case match, using definition of filter
| x > y = (s . m (+1)) Nil_
| x <= y = if p x
           then (s . m (+1)) (Cons_ x (f' (x+1, y)))
		   else f' (x+1, y)
-- Dfn of m
| x > y = s Nil_
| x <= y = if p x
           then s (Cons_ (x+1) (f' (x+1, y)))
           else f' (x+1, y)
-- Dfn of s
| x > y = 0
| x <= y = if p x
           then (x+1) + f' (x+1, y)
           else f' (x+1, y)
```
$\blacksquare$