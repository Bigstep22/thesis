{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -dsuppress-all -dno-suppress-type-signatures -dno-typeable-binds -dsuppress-uniques #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
import Test.Tasty.Bench


f :: (Int, Int) -> Int
f = sum1 . map1 (+1) . filter1 odd . between1

f' :: (Int, Int) -> Int
f' (x, y) = loop x
  where
    loop x | x > y = 0
           | otherwise = if odd x
                       then (x + 1) + loop (x + 1)
                       else loop (x + 1)

-- main = print (f' (1, 10))



-- data List_ a b = Nil_ | Cons_ a b deriving Functor
-- data List a = Nil | Cons a (List a) deriving Functor


-- data Church F = Ch (forall A . (f A -> A) -> A)

data Tree a = Empty
            | Leaf a
            | Fork (Tree a) (Tree a)
data Tree_ a b = Empty_
               | Leaf_ a
               | Fork_ b b
data TreeCh a = TreeCh (forall b . (Tree_ a b -> b) -> b)

toCh :: Tree a -> TreeCh a
toCh t = TreeCh (\a -> fold a t)
fold :: (Tree_ a b -> b) -> Tree a -> b
fold a Empty      = a Empty_
fold a (Leaf x)   = a (Leaf_ x)
fold a (Fork l r) = a (Fork_ (fold a l)
                             (fold a r))

fromCh :: TreeCh a -> Tree a
fromCh (TreeCh fold) = fold in'
in' :: Tree_ a (Tree a) -> Tree a
in' Empty_ = Empty
in' (Leaf_ x) = Leaf x
in' (Fork_ l r) = Fork l r

{-# RULES "toCh/fromCh fusion"
   forall x. toCh (fromCh x) = x #-}
{-# INLINE [0] toCh #-}
{-# INLINE [0] fromCh #-}

data TreeCoCh a = forall s . TreeCoCh (s -> Tree_ a s) s
toCoCh :: Tree a -> TreeCoCh a
toCoCh = TreeCoCh out
out Empty = Empty_
out (Leaf a) = Leaf_ a
out (Fork l r) = Fork_ l r

fromCoCh :: TreeCoCh a -> Tree a
fromCoCh (TreeCoCh h s) = unfold h s
unfold h s = case h s of
  Empty_ -> Empty
  Leaf_ a -> Leaf a
  Fork_ sl sr -> Fork (unfold h sl) (unfold h sr)

{-# RULES "toCh/fromCh fusion"
   forall x. toCoCh (fromCoCh x) = x #-}
{-# INLINE [0] toCoCh #-}
{-# INLINE [0] fromCoCh #-}



-- between
between1 :: (Int, Int) -> Tree Int
between1 (x, y) = case compare x y of
  GT -> Empty
  EQ -> Leaf x
  LT -> Fork (between1 (x, mid))
               (between1 (mid + 1, y))
  where mid = (x + y) `div` 2

b :: (Tree_ Int b -> b) -> (Int, Int) -> b
b a (x, y) = case compare x y of
  GT -> a Empty_
  EQ -> a (Leaf_ x)
  LT -> a (Fork_ (b a (x, mid))
                 (b a (mid + 1, y)))
  where mid = (x + y) `div` 2
betweenCh :: (Int, Int) -> TreeCh Int
betweenCh (x, y) = TreeCh (\a -> b a (x, y))

between2 :: (Int, Int) -> Tree Int
between2 = fromCh . betweenCh
{-# INLINE between2 #-}

h :: (Int, Int) -> Tree_ Int (Int, Int)
h (x, y) = case compare x y of
  GT -> Empty_
  EQ -> Leaf_ x
  LT -> Fork_ (x, mid) (mid + 1, y)
  where mid = (x + y) `div` 2

between3 :: (Int, Int) -> Tree Int
between3 = fromCoCh . TreeCoCh h
{-# INLINE between3 #-}

-- append
append1 :: Tree a -> Tree a -> Tree a
append1 t1 Empty = t1
append1 Empty t2 = t2
append1 t1 t2 = Fork t1 t2

appendCh :: TreeCh a -> TreeCh a -> TreeCh a
appendCh (TreeCh g1) (TreeCh g2) =
    TreeCh (\a -> a (Fork_ (g1 a) (g2 a)))
append2 :: Tree a -> Tree a -> Tree a
append2 t1 t2 = fromCh (appendCh (toCh t1) (toCh t2))
{-# INLINE append2 #-}

appendCoCh :: TreeCoCh a -> TreeCoCh a -> TreeCoCh a
appendCoCh (TreeCoCh h1 s1) (TreeCoCh h2 s2) = TreeCoCh h' Nothing
  where h' Nothing = Fork_ (Just (TreeCoCh h1 s1))
                           (Just (TreeCoCh h2 s2))
        h' (Just (TreeCoCh h s)) = case h s of
          Empty_ -> Empty_
          Leaf_ a -> Leaf_ a
          Fork_ l r -> Fork_ (Just (TreeCoCh h l))
                             (Just (TreeCoCh h r))
append3 :: Tree a -> Tree a -> Tree a
append3 t1 t2 = fromCoCh (appendCoCh (toCoCh t1) (toCoCh t2))
{-# INLINE append3 #-}
-- {-# RULES
-- "append -> fused" [~1] forall t1 t2.
--   append1 t1 t2 =
--     fromCh (appendCh (toCh t1) (toCh t2))
-- "append -> unfused" [1] forall t1 t2.
--   fromCh (appendCh (toCh t1) (toCh t2)) =
--     append1 t1 t2 #-}
-- This offers 10% speedup in the scenario when a fused
-- pipeline has been built, but fusion has not been enabled
-- 393 +- 14 micro seconds vs.
-- 434 +- 42 micro seconds.

-- filter
filter1 :: (a -> Bool) -> Tree a -> Tree a
filter1 p Empty = Empty
filter1 p (Leaf a) = if p a then Leaf a else Empty
filter1 p (Fork l r) = append1 (filter1 p l) (filter1 p r)

filt :: (a -> Bool) -> Tree_ a c -> Tree_ a c
filt p Empty_ = Empty_
filt p (Leaf_ x) = if p x then Leaf_ x else Empty_
filt p (Fork_ l r) = Fork_ l r

filterCh :: (a -> Bool) -> TreeCh a -> TreeCh a
filterCh p (TreeCh g) = TreeCh (\a -> g (a . filt p))
filter2 :: (a -> Bool) -> Tree a -> Tree a
filter2 p = fromCh . filterCh p . toCh
{-# INLINE filter2 #-}

filterCoCh :: (a -> Bool) -> TreeCoCh a -> TreeCoCh a
filterCoCh p (TreeCoCh h s) = TreeCoCh (filt p . h) s
filter3 :: (a -> Bool) -> Tree a -> Tree a
filter3 p = fromCoCh . filterCoCh p . toCoCh
{-# INLINE filter3 #-}

-- map
map1 :: (a -> b) -> Tree a -> Tree b
map1 f Empty = Empty
map1 f (Leaf a) = Leaf (f a)
map1 f (Fork l r) = append1 (map1 f l) (map1 f r)

m :: (a -> b) -> Tree_ a c -> Tree_ b c
m f Empty_ = Empty_
m f (Leaf_ a) = Leaf_ (f a)
m f (Fork_ l r) = Fork_ l r

mapCh :: (a -> b) -> TreeCh a -> TreeCh b
mapCh f (TreeCh g) = TreeCh (\a -> g (a . m f))
map2 :: (a -> b) -> Tree a -> Tree b
map2 f = fromCh . mapCh f . toCh
{-# INLINE map2 #-}

mapCoCh :: (a -> b) -> TreeCoCh a -> TreeCoCh b
mapCoCh f (TreeCoCh h s) = TreeCoCh (m f . h) s
map3 :: (a -> b) -> Tree a -> Tree b
map3 f = fromCoCh . mapCoCh f . toCoCh
{-# INLINE map3 #-}

-- sum
sum1 :: Tree Int -> Int
sum1 Empty = 0
sum1 (Leaf x) = x
sum1 (Fork x y) = sum1 x + sum1 y

s :: Tree_ Int Int -> Int
s Empty_ = 0
s (Leaf_ x) = x
s (Fork_ x y) = x + y

sumCh :: TreeCh Int -> Int
sumCh (TreeCh g) = g s
sum2 :: Tree Int -> Int
sum2 = sumCh . toCh
{-# INLINE sum2 #-}

{-
Implementing the below function as tail recursive using
an accumulator and list of remaining computations does not
result in a tail recursive Core representation using gotos...
-}
sumCoCh :: TreeCoCh Int -> Int
sumCoCh (TreeCoCh h s') = loop 0 [s']
  where loop sum (s:ss) = case h s of
          Empty_ -> loop sum ss
          Leaf_ x -> loop (sum+x) ss
          Fork_ l r -> loop sum (l:r:ss)
        loop sum [] = sum
sum3 :: Tree Int -> Int
sum3 = sumCoCh . toCoCh
{-# INLINE sum3 #-}



pipeline1 = sum1 . map1 (+2) . filter1 odd . between1
pipeline2 = sum2 . map2 (+2) . filter2 odd . between2
pipeline3 = sum3 . map3 (+2) . filter3 odd . between3

sumApp1 (x, y)  = sum1 (append1 (between1 (x, y)) (between1 (x, y)))
sumApp2 (x, y)  = sum2 (append2 (between2 (x, y)) (between2 (x, y)))
sumApp3 (x, y)  = sum3 (append3 (between3 (x, y)) (between3 (x, y)))

input = (1, 10000)
-- main = print (pipeline2 input)
main = defaultMain
  [
    bgroup "Filter pipeline"
    [ bench "pipcofused1" $ nf pipeline3 input
    , bench "pipcofused2" $ nf pipeline3 input
    , bench "pipcofused3" $ nf pipeline3 input
    , bench "pipcofused4" $ nf pipeline3 input
    , bench "pipchfused1" $ nf pipeline2 input
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
  ]

-- With tastybench
{- chfused
Rec {
$s$wb :: Int -> Int# -> Int
$s$wb
  = \ (ww :: Int) (ww1 :: Int#) ->
      case ww of wild { I# x ->
      case ># x ww1 of {
        __DEFAULT ->
          case ==# x ww1 of {
            __DEFAULT ->
              case <# x ww1 of {
                __DEFAULT -> case lvl7 of wild1 { };
                1# ->
                  let {
                    mid :: Int#
                    mid = uncheckedIShiftRA# (+# x ww1) 1# } in
                  case $s$wb wild mid of { I# x1 ->
                  case $s$wb (I# (+# mid 1#)) ww1 of { I# y -> I# (+# x1 y) }
                  }
              };
            1# ->
              case remInt# x 2# of {
                __DEFAULT -> I# (+# x 2#);
                0# -> lvl4
              }
          };
        1# -> lvl4
      }
      }
end Rec }
-}
{- cofused
Rec {
$wloop :: Int# -> Int# -> Int#
$wloop
  = \ (ww :: Int#) (ww1 :: Int#) ->
      case ># ww ww1 of {
        __DEFAULT ->
          case ==# ww ww1 of {
            __DEFAULT ->
              case <# ww ww1 of {
                __DEFAULT -> case lvl3 of wild { };
                1# ->
                  let {
                    mid :: Int#
                    mid = uncheckedIShiftRA# (+# ww ww1) 1# } in
                  case $wloop ww mid of ww2 { __DEFAULT ->
                  case $wloop (+# mid 1#) ww1 of ww3 { __DEFAULT -> +# ww2 ww3 }
                  }
              };
            1# ->
              case remInt# ww 2# of {
                __DEFAULT -> +# ww 2#;
                0# -> 0#
              }
          };
        1# -> 0#
      }
end Rec }
-}