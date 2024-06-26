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
b :: (List_ Int b -> b) -> (Int, Int) -> b
b a (x, y) = loop (x, y)
  where loop (x, y) = case x > y of
    True -> a Nil_
    False -> a (Cons_ x (loop (x+1,y)))
betweenCh :: (Int, Int) -> ListCh Int
betweenCh (x, y) = ListCh (\a -> b a (x, y))

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

s :: List_ Int Int -> Int
s Nil_ = 0
s (Cons_ x y) = x + y
sumCh :: ListCh Int -> Int
sumCh (ListCh g) = g s
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
-- Inlining of betweenCh
sumCh . mapCh (+1) . filterCh odd . ListCh (\a -> b a (x, y))
-- Dfn of filterCh + beta reduction
sumCh . mapCh (+1) .
  ListCh (\a' ->
    (\a -> b a (x, y))
	(\x -> case x of
      Nil_ -> a' Nil_
      Cons_ x xs -> if (p x) then a' (Cons_ x xs) else xs
    )
  )
-- Beta reduction
sumCh . mapCh (+1) .
  ListCh (\a' ->
    b (\x -> case x of
      Nil_ -> a' Nil_
      Cons_ x xs -> if (p x) then a' (Cons_ x xs) else xs
    )
	(x, y))
-- Dfn of mapCh + beta reduction
sumCh . ListCh (\a ->
  (\a' ->
    b (\x -> case x of
      Nil_ -> a' Nil_
      Cons_ x xs -> if (p x) then a' (Cons_ x xs) else xs
    )
	(x, y)
  )
  (a . m (+1)))
-- Substitution
sumCh . ListCh (\a ->
  b (\x -> case x of
    Nil_ -> (a . m (+1)) Nil_
    Cons_ x xs -> if (p x) then (a . m (+1)) (Cons_ x xs) else xs
  )
  (x, y))
-- Dfn of sumCh
(\a ->
  b (\x -> case x of
    Nil_ -> (a . m (+1)) Nil_
    Cons_ x xs -> if (p x) then (a . m (+1)) (Cons_ x xs) else xs
  )
  (x, y)
) s
-- Beta reduction
b (\x -> case x of
  Nil_ -> s (m (+1) Nil_)
  Cons_ x xs -> if (p x) then s (m (+1) (Cons_ x xs)) else xs
) (x, y)
-- Inlining m + beta reduction
b (\x -> case x of
  Nil_ -> s Nil_
  Cons_ x xs -> if (p x) then s (Cons_ ((+1) x) xs) else xs
) (x, y)
-- Inlining s + beta reduction
b (\x -> case x of
  Nil_ -> 0
  Cons_ x xs -> if (p x) then ((+1) x) + xs) else xs
) (x, y)
-- Inlining of b + beta reduction
loop (x, y) = case x > y of
  True -> case Nil_ of
    Nil_ -> 0
    Cons_ x xs -> if (p x) then ((+1) x) + xs) else xs
  False -> case (Cons_ x (loop (x+1,y))) of
    Nil_ -> 0
    Cons_ x xs -> if (p x) then ((+1) x) + xs) else xs
loop (x, y)
-- case-of-known-case optimization
loop (x, y) = case x > y of
  True -> 0
  False -> if (p x) then ((+1) x) + loop (x+1,y)) else loop (x+1,y)
loop (x, y)
-- Cleaning it up:
loop (x, y) = if x > y 
              then 0
              else if (p x)
                   then x+1 + loop (x+1, y)
		           else loop (x+1, y)
loop (x, y)
```
$\blacksquare$