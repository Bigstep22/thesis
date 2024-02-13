{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
import Test.Tasty.Bench


{-
f :: (Int, Int) -> Int
f = sum1 . map1 (+1) . filter1 odd . between1

f' :: (Int, Int) -> Int
f' (x, y) = loop x
  where
    loop x | x > y = 0
           | otherwise = if odd x
                       then (x + 1) + loop (x + 1)
                       else loop (x + 1)
-}
-- main = print "Hello"



data List_ a b = Nil_ | NilT_ b | Cons_ a b deriving Functor
data List a = Nil | Cons a (List a) deriving (Functor, Show)
data ListCh a = ListCh (forall b . (List_ a b -> b) -> b)

toCh :: List a -> ListCh a
toCh t = ListCh (\a -> fold a t)
fold :: (List_ a b -> b) -> List a -> b
fold a Nil      = a Nil_
fold a (Cons x xs) = a (Cons_ x (fold a xs))

fromCh :: ListCh a -> List a
fromCh (ListCh fold) = fold in'
in' :: List_ a (List a) -> List a
in' Nil_ = Nil
in' (NilT_ b) = b
in' (Cons_ x xs) = Cons x xs

{-# RULES "toCh/fromCh fusion"
   forall x. toCh (fromCh x) = x #-}
{-# INLINE [0] toCh #-}
{-# INLINE [0] fromCh #-}

-- between
between1 :: (Int, Int) -> List Int
between1 (x, y)
  | x > y  = Nil
  | x <= y  = Cons x (between1 (x+1,y))
  where mid = (x + y) `div` 2

b :: (List_ Int b -> b) -> (Int, Int) -> b
b a (x, y)
  | x > y   = a Nil_
  | x <= y  = a (Cons_ x (b a (x+1,y)))
betweenCh :: (Int, Int) -> ListCh Int
betweenCh (x, y) = ListCh (\a -> b a (x, y))

between2 :: (Int, Int) -> List Int
between2 = fromCh . betweenCh
{-# INLINE between2 #-}


-- filter
filter1 :: (a -> Bool) -> List a -> List a
filter1 p Nil = Nil
filter1 p (Cons x xs) = if p x then Cons x (filter1 p xs) else filter1 p xs

filt :: (a -> Bool) -> List_ a c -> List_ a c
filt p Nil_ = Nil_
filt p (NilT_ xs) = NilT_ xs
filt p (Cons_ x xs) = if p x then Cons_ x xs else NilT_ xs

filterCh :: (a -> Bool) -> ListCh a -> ListCh a
filterCh p (ListCh g) = ListCh (\a -> g (a . filt p))
filter2 :: (a -> Bool) -> List a -> List a
filter2 p = fromCh . filterCh p . toCh
{-# INLINE filter2 #-}

-- map
map1 :: (a -> b) -> List a -> List b
map1 f Nil = Nil
map1 f (Cons x xs) = Cons (f x) (map1 f xs)

m :: (a -> b) -> List_ a c -> List_ b c
m f Nil_ = Nil_
m f (NilT_ xs) = NilT_ xs
m f (Cons_ x xs) = Cons_ (f x) xs

mapCh :: (a -> b) -> ListCh a -> ListCh b
mapCh f (ListCh g) = ListCh (\a -> g (a . m f))
map2 :: (a -> b) -> List a -> List b
map2 f = fromCh . mapCh f . toCh
{-# INLINE map2 #-}

-- sum
sum1 :: List Int -> Int
sum1 Nil = 0
sum1 (Cons x xs) = x + sum1 xs

s :: List_ Int Int -> Int
s Nil_ = 0
s (NilT_ x) = x
s (Cons_ x y) = x + y

sumCh :: ListCh Int -> Int
sumCh (ListCh g) = g s
sum2 :: List Int -> Int
sum2 = sumCh . toCh
{-# INLINE sum2 #-}



pipeline1 = sum1 . map1 (+1) . filter1 odd . between1
pipeline2 = sum2 . map2 (+1) . filter2 odd . between2
-- pipeline3 = sum3 . map3 (+1) . filter3 odd . between3

-- sumApp1 (x, y)  = sum1 (append1 (between1 (x, y)) (between1 (x, y)))
-- sumApp2 (x, y)  = sum2 (append2 (between2 (x, y)) (between2 (x, y)))
-- sumApp3 (x, y)  = sum3 (append3 (between3 (x, y)) (between3 (x, y)))

input = (1, 10)
main = print (pipeline2 input)
{-
main = defaultMain
  [
    bgroup "Filter pipeline"
    [ 
    --   bench "pipcofused1" $ nf pipeline3 input
    -- , bench "pipcofused2" $ nf pipeline3 input
    -- , bench "pipcofused3" $ nf pipeline3 input
    -- , bench "pipcofused4" $ nf pipeline3 input
     bench "pipchfused1" $ nf pipeline2 input
    , bench "pipchfused2" $ nf pipeline2 input
    , bench "pipchfused3" $ nf pipeline2 input
    , bench "pipchfused4" $ nf pipeline2 input
    , bench "pipunfused1" $ nf pipeline1 input
    , bench "pipunfused2" $ nf pipeline1 input
    , bench "pipunfused3" $ nf pipeline1 input
    , bench "pipunfused4" $ nf pipeline1 input
    ]
    -- ,
    -- bgroup "Sum-append pipeline"
    -- [
    --    bench "sumcofused1" $ nf sumApp3 input             
    -- ,  bench "sumcofused2" $ nf sumApp3 input             
    -- ,  bench "sumcofused3" $ nf sumApp3 input             
    -- ,  bench "sumcofused4" $ nf sumApp3 input             
    -- ,  bench "sumchfused1" $ nf sumApp2 input
    -- ,  bench "sumchfused2" $ nf sumApp2 input
    -- ,  bench "sumchfused3" $ nf sumApp2 input
    -- ,  bench "sumchfused4" $ nf sumApp2 input
    -- ,  bench "sumunfused1" $ nf sumApp1 input
    -- ,  bench "sumunfused2" $ nf sumApp1 input
    -- ,  bench "sumunfused3" $ nf sumApp1 input
    -- ,  bench "sumunfused4" $ nf sumApp1 input
    -- ]
  ]-}
