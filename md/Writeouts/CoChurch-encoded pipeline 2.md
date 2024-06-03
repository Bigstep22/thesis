I will present the \textit{idea} behind Cochurch encodings:
```haskell
data List'_ a b = Nil'_ | NilT'_ b | Cons'_ a b deriving Functor
data List a = Nil | Cons a (List a) deriving (Functor, Show)
data ListCoCh a = forall s . ListCoCh (s -> List'_ a s) s

toCoCh :: List a -> ListCoCh a
toCoCh = ListCoCh out
out :: List a -> List'_ a (List a)
out Nil = Nil'_
out (Cons x xs) = Cons'_ x xs

fromCoCh :: ListCoCh a -> List a
fromCoCh (ListCoCh h s) = unfold h s
unfold :: (b -> List'_ a b) -> b -> List a
unfold h s = case h s of
  Nil'_ -> Nil
  NilT'_ xs -> unfold h xs
  Cons'_ x xs -> Cons x (unfold h xs)
```
CoChurch encoded versions of sum, map (+2), filter odd, and between look like the following:
```haskell
su' :: (s -> List'_ Int s) -> s -> Int
su' h s = loop s
  where loop s' = case h s' of
    Nil'_ -> 0
    NilT'_ xs -> loop xs
    Cons'_ x xs -> x + loop xs
sumCoCh :: ListCoCh Int -> Int
sumCoCh (ListCoCh h s) = su' h s

m' :: (a -> b) -> List'_ a c -> List'_ b c
m' f (Cons'_ x xs) = Cons'_ (f x) xs
m' _ (NilT'_ xs) = NilT'_ xs
m' _ (Nil'_) = Nil'_
mapCoCh :: (a -> b) -> ListCoCh a -> ListCoCh b
mapCoCh f (ListCoCh h s) = ListCoCh (m' f . h) s

filt p h s = case h s of
               Nil'_ -> Nil'_
               NilT'_ xs -> NilT'_ xs
               Cons'_ x xs -> if p x then Cons'_ x xs else NilT'_ xs
filterCoCh :: (a -> Bool) -> ListCoCh a -> ListCoCh a
filterCoCh p (ListCoCh h s) = ListCoCh (filt p h) s

betweenCoCh :: (Int, Int) -> List'_ Int (Int, Int)
betweenCoCh (x, y) = case x > y of
  case True -> Nil'_
  case False -> Cons'_ x (x+1, y)
```
Next, the actual functions:
```haskell
sum :: List Int -> Int
sum = sumCoCh . toCoCh

map :: (a -> b) -> List a -> List b
map f = fromCoCh . mapCoCh f . toCoCh

filter :: (a -> Bool) -> List a -> List a
filter p = fromCoCh . filterCoCh p . toCoCh

between :: (Int, Int) -> List Int
between = fromCoCh . ListCoCh betweenCoCh
```
Remember the pipeline? Now it looks like this:
```haskell
f = sum . map (+2) . filter odd . between

f =        sumCoCh        . toCoCh .
fromCoCh . mapCoCh (+2)   . toCoCh .
fromCoCh . filterCoCh odd . toCoCh .
fromCoCh . ListCoCh betweenCoCh
```
When 'fused' it looks like this:
```haskell
sumCoCh . mapCoCh (+2) . filterCoCh odd . ListCoCh betweenCoCh
```
For some input (x, y):
```haskell
sumCoCh . mapCoCh (+2) . filterCoCh odd . ListCoCh betweenCoCh (x, y)
-- Dfn of filterCoCh + beta reduction
sumCoCh . mapCoCh (+2) . ListCoCh (filt odd betweenCoCh) (x, y)
-- Dfn of mapCoCh + beta reduction
sumCoCh . ListCoCh (m' (+2) . filt odd betweenCoCh) (x, y)
-- Dfn of sumCoCh + beta reduction
su' (m' (+2) . filt odd betweenCoCh) (x, y)
-- Dfn of su' + beta reduction
loop (x, y) = case ((m' (+2) . filt odd betweenCoCh) (x, y)) of
  Nil'_ -> 0
  NilT'_ s -> loop s
  Cons'_ x s -> x + loop s
loop (x, y)
-- Dfn of filt + beta reduction
loop (x, y) = case (m' (+2) . (
                case betweenCoCh (x, y) of 
                    Nil'_ -> Nil'_
                    NilT'_ xs -> NilT'_ xs
                    Cons'_ x xs -> if odd x then Cons'_ x xs else NilT'_ xs
  )) of
  Nil'_ -> 0
  NilT'_ s -> loop s
  Cons'_ x s -> x + loop s
loop (x, y)
-- Dfn of betweenCoCh + beta reduction
loop (x, y) = case (m' (+2) . (
                case (
                  case (x > y) of
                    True -> Nil'_
                    False -> Cons'_ x (x+1, y)
                  ) of 
                  Nil'_ -> Nil'_
                  NilT'_ xs -> NilT'_ xs
                  Cons'_ x xs -> if odd x then Cons'_ x xs else NilT'_ xs
                )) of
  Nil'_ -> 0
  NilT'_ s -> loop s
  Cons'_ x s -> x + loop s
loop (x, y)
-- Case-of-case optimization
loop (x, y) = case (m' (+2) . (
                case (x > y) of
                  True -> case (Nil'_) of
                    Nil'_ -> Nil'_
                    NilT'_ xs -> NilT'_ xs
                    Cons'_ x xs -> if odd x then Cons'_ x xs else NilT'_ xs
                  False -> case (Cons'_ x (x+1, y)) of
                    Nil'_ -> Nil'_
                    NilT'_ xs -> NilT'_ xs
                    Cons'_ x xs -> if odd x then Cons'_ x xs else NilT'_ xs
                )) of
  Nil'_ -> 0
  NilT'_ s -> loop s
  Cons'_ x s -> x + loop s
loop (x, y)
-- Case-of-known-case optimization
loop (x, y) = case (m' (+2) (case (x > y) of
    True -> Nil'_
    False -> if odd x then Cons'_ x (x+1, y) else NilT'_ (x+1, y)
  )) of
  Nil'_ -> 0
  NilT'_ s -> loop s
  Cons'_ x s -> x + loop s
loop (x, y)
-- Dfn of m' + beta reduction
loop (x, y) = case (
                case (
                  case (x > y) of
                    True -> Nil'_
                    False -> if odd x then Cons'_ x (x+1, y) else NilT'_ (x+1, y)
                ) of
                  Cons'_ x xs -> Cons'_ ((+2) x) xs
                  NilT'_ xs -> NilT'_ xs
                  Nil'_ => Nil'_
              ) of
                Nil'_ -> 0
                NilT'_ s -> loop s
                Cons'_ x s -> x + loop s
loop (x, y)
-- Case-of-case optimization
loop (x, y) = case (
                case (x > y) of
                  True -> case (Nil'_) of
                    Cons'_ x xs -> Cons'_ ((+2) x) xs
                    NilT'_ xs -> NilT'_ xs
                    Nil'_ => Nil'_
                  False -> case (if odd x then Cons'_ x (x+1, y) else NilT'_ (x+1, y)) of
                    Cons'_ x xs -> Cons'_ ((+2) x) xs
                    NilT'_ xs -> NilT'_ xs
                    Nil'_ => Nil'_
              ) of
                Nil'_ -> 0
                NilT'_ s -> loop s
                Cons'_ x s -> x + loop s
loop (x, y)
-- Case-of-known-case optimization
loop (x, y) = case (
                case (x > y) of
                  True -> Nil'_
                  False -> case (if odd x then Cons'_ x (x+1, y) else NilT'_ (x+1, y)) of
                    Cons'_ x xs -> Cons'_ ((+2) x) xs
                    NilT'_ xs -> NilT'_ xs
                    Nil'_ => Nil'_
              ) of
                Nil'_ -> 0
                NilT'_ s -> loop s
                Cons'_ x s -> x + loop s
loop (x, y)
-- Dfn of if + beta reduction
loop (x, y) = case (
                case (x > y) of
                  True -> Nil'_
                  False -> case (
                    case (odd x) of
                      True -> Cons'_ x (x+1, y) 
                      False -> NilT'_ (x+1, y)
                  ) of
                    Cons'_ x xs -> Cons'_ ((+2) x) xs
                    NilT'_ xs -> NilT'_ xs
                    Nil'_ => Nil'_
              ) of
                Nil'_ -> 0
                NilT'_ s -> loop s
                Cons'_ x s -> x + loop s
loop (x, y)
-- case-of-case optimization
loop (x, y) = case (
                case (x > y) of
                  True -> Nil'_
                  False ->  case (odd x) of
                    True -> case (Cons'_ x (x+1, y)) of
                      Cons'_ x xs -> Cons'_ ((+2) x) xs
                      NilT'_ xs -> NilT'_ xs
                      Nil'_ => Nil'_
                    False -> case (NilT'_ (x+1, y)) of
                      Cons'_ x xs -> Cons'_ ((+2) x) xs
                      NilT'_ xs -> NilT'_ xs
                      Nil'_ => Nil'_
              ) of
                Nil'_ -> 0
                NilT'_ s -> loop s
                Cons'_ x s -> x + loop s
loop (x, y)
-- Case-of-known-case optimization
loop (x, y) = case (
                case (x > y) of
                  True -> Nil'_
                  False ->  case (odd x) of
                    True -> Cons'_ ((+2) x) (x+1, y)
                    False -> NilT'_ (x+1, y)
              ) of
                Nil'_ -> 0
                NilT'_ s -> loop s
                Cons'_ x s -> x + loop s
loop (x, y)
-- case-of-case optimization
loop (x, y) = case (x > y) of
                True -> case (Nil'_) of
                  Nil'_ -> 0
                  NilT'_ s -> loop s
                  Cons'_ x s -> x + loop s
                False -> case (
                  case (odd x) of
                    True -> Cons'_ ((+2) x) (x+1, y)
                    False -> NilT'_ (x+1, y)
                ) of
                  Nil'_ -> 0
                  NilT'_ s -> loop s
                  Cons'_ x s -> x + loop s
loop (x, y)
-- Case-of-known-case optimization
loop (x, y) = case (x > y) of
                True -> 0
                False -> case (
                  case (odd x) of
                    True -> Cons'_ ((+2) x) (x+1, y)
                    False -> NilT'_ (x+1, y)
                ) of
                  Nil'_ -> 0
                  NilT'_ s -> loop s
                  Cons'_ x s -> x + loop s
loop (x, y)
-- case-of-case optimization
loop (x, y) = case (x > y) of
                True -> 0
                False -> case (odd x) of
                  True -> case (Cons'_ ((+2) x) (x+1, y)) of
                    Nil'_ -> 0
                    NilT'_ s -> loop s
                    Cons'_ x s -> x + loop s
                  False -> case (NilT'_ (x+1, y)) of
                    Nil'_ -> 0
                    NilT'_ s -> loop s
                    Cons'_ x s -> x + loop s
loop (x, y)
-- Case-of-known-case optimization
loop (x, y) = case (x > y) of
                True -> 0
                False -> case (odd x) of
                  True -> ((+2) x) + loop (x + 1, y)
                  False -> loop (x + 1, y)
loop (x, y)
-- Boom! Finally a sane path to solution
loop (x, y) = case (x > y) of
                True -> 0
                False -> case (odd x) of
                  True -> (x+2) + loop (x+1, y)
                  False -> loop (x+1, y)
loop (x, y)
-- With some nicer syntax, compiles to same case of case tree:
loop (x, y) = if (x > y)
              then 0
              else if (odd x)
                   then (x + 2) + loop (x+1, y)
                   else -> loop (x+1, y)
loop (x, y)
```
$\blacksquare$
Here is the proof that toCoCh and fromCoCh are mutually inverse:
```haskell
fromCoCh . toCoCh l
-- Dfn of toCoCh + beta reduction
fromCoCh . ListCoCh out l
-- Dfn of fromCoCh + beta reduction
unfold out l
-- Dfn of unfold + beta reduction
case out l of
  Nil'_ -> Nil
  NilT'_ xs -> unfold out xs
  Cons'_ x xs -> Cons x (unfold out xs)
-- Dfn of out + beta reduction
case (
  case l of
    Nil -> Nil'_
    Cons x xs -> Cons'_ x xs
  ) of
  Nil'_ -> Nil
  NilT'_ xs -> unfold out xs
  Cons'_ x xs -> Cons x (unfold out xs)
-- case-of-case
case l of
  Nil -> case Nil'_ of
    Nil'_ -> Nil
    NilT'_ xs -> unfold out xs
    Cons'_ x xs -> Cons x (unfold out xs)
  Cons x xs -> case Cons'_ x xs
    Nil'_ -> Nil
    NilT'_ xs -> unfold out xs
    Cons'_ x xs -> Cons x (unfold out xs)
-- case-of-known-case
case l of
  Nil -> Nil
  Cons x xs -> Cons x (unfold out xs)
-- Function is same as id through induction.


toCoCh . fromCoCh (ListCoCh h s)
-- Unfold fromCoCh
toCoCh . unfold h s
-- Dfn of toCoCh
ListCoCh out (unfold h s)
-- This is true, so long as parametricity holds, see second proof of page 51 of Harper
```
It seems as if the end function is forced to be recursive in this simple fashion, no further unfolding is needed. In the Church-encoded version we manually had to identify an f' such that we had a cleanly recursing function. I wonder if this is the source of why Cochurch-encoded function is faster.
This simple recursive function has its roots in the definition of su'. I'm going to try to tweak it to see if I can suplify that function further (removing there where).
- It turns out that removing the where creates a big slowdown (about 3x), making the function about twice as slow as the church-encoding.
Further questions:
- Can I implement the filter function without employing a ConsN'_ type member?
	- I don't believe so, one of the preconditions for the faithful implementation of a CoChurch encoding is that the original function if a natural transformation, this is not the case for the filter function on lists (it is, however, for leaf trees, the example given in the paper.). I.e. filter is not a structure preserving function. Map is.
- Is the story I thought of above reflected in the specialized core-representation functions output by Haskell?
	- Haskell makes a specialized version of the final function for the CoChurch encoded pipeline, but doesn't seem to do so for the Church-encoded pipeline.