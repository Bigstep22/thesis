\long\def\ignore#1{}
\ignore{
\begin{code}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -dsuppress-all -dno-suppress-type-signatures -dno-typeable-binds -dsuppress-uniques #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
import Prelude hiding (foldr)
import Test.Tasty.Bench
import GHC.List
\end{code}
}
\subsubsection{Lists}
In this section further replication of \cite{Harper2011}'s work is described, but instead of implementing Leaf trees, Lists are implemented.

This was done to see how the descriptions in \cite{Harper2011}'s work generalize and to have a simpler datastructure on which to perform analysis; seeing how and when the fusion works and when it doesn't.

We again start with the datatype descriptions. We use \tt{List'} instead of \tt{List} as there is a namespace collision with GHC's \tt{List} datatype:
\begin{code}
data List' a = Nil | Cons a (List' a)
data List_ a b = Nil_ | Cons_ a b
\end{code}
\paragraph{(Co)Church-encodings} The church encoding, proper encoding and decoding functions, and fusion pragmas are defined:
\begin{code}
data ListCh a = ListCh (forall b . (List_ a b -> b) -> b)
toCh :: List' a -> ListCh a
toCh t = ListCh (\a -> fold a t)
fold :: (List_ a b -> b) -> List' a -> b
fold a Nil         = a Nil_
fold a (Cons x xs) = a (Cons_ x (fold a xs))
fromCh :: ListCh a -> List' a
fromCh (ListCh fold') = fold' in'
in' :: List_ a (List' a) -> List' a
in' Nil_ = Nil
in' (Cons_ x xs) = Cons x xs
{-# RULES "toCh/fromCh fusion"
   forall x. toCh (fromCh x) = x #-}
{-# INLINE [0] toCh #-}
{-# INLINE [0] fromCh #-}
\end{code}
A generalized natural transformation function is defined:
\begin{code}
natCh :: (forall c . List_ a c -> List_ b c) -> ListCh a -> ListCh b
natCh f (ListCh g) = ListCh (\a -> g (a . f))
\end{code}
The cochurch encodings are defined similarly:
\begin{code}
data ListCoCh a = forall s . ListCoCh (s -> List_ a s) s
toCoCh :: List' a -> ListCoCh a
toCoCh = ListCoCh out
out :: List' a -> List_ a (List' a)
out Nil = Nil_
out (Cons x xs) = Cons_ x xs
fromCoCh :: ListCoCh a -> List' a
fromCoCh (ListCoCh h s) = unfold h s
unfold :: (b -> List_ a b) -> b -> List' a
unfold h s = case h s of
  Nil_ -> Nil
  Cons_ x xs -> Cons x (unfold h xs)
{-# RULES "toCh/fromCh fusion"
   forall x. toCoCh (fromCoCh x) = x #-}
{-# INLINE [0] toCoCh #-}
{-# INLINE [0] fromCoCh #-}
\end{code}
A generalized natural transformation function is defined:
\begin{code}
natCoCh :: (forall c . List_ a c -> List_ b c) -> ListCoCh a -> ListCoCh b
natCoCh f (ListCoCh h s) = ListCoCh (f . h) s
\end{code}
\paragraph{Between}
The between function is defined in three different fashions: Normally, with the Church-encoding, and with the Cochurch encoding.
We leverage \tt{INLINE} pragmas to make sure that the fusion pragmas can effectively work.
For the non-encoded implementation, we simply leverage recursion:
\begin{code}
between1 :: (Int, Int) -> List' Int
between1 (x, y) = case x > y of
  True  -> Nil
  False -> Cons x (between1 (x+1,y))
{-# INLINE between1 #-}
\end{code}
For the Church-encoded version we define a recursion principle \tt{b} and use that to define the encoded church function:
\begin{code}
b :: (List_ Int b -> b) -> (Int, Int) -> b
b a (x, y) = case x > y of
  True -> a Nil_
  False -> a (Cons_ x (b a (x+1,y)))
betweenCh :: (Int, Int) -> ListCh Int
betweenCh (x, y) = ListCh (\a -> b a (x, y))
between2 :: (Int, Int) -> List' Int
between2 = fromCh . betweenCh
{-# INLINE between2 #-}
\end{code}
For the Cochurch-encoded version we define a coalgebra:
\begin{code}
betweenCoCh :: (Int, Int) -> List_ Int (Int, Int)
betweenCoCh (x, y) = case x > y of
  True -> Nil_
  False -> Cons_ x (x+1, y)
between3 :: (Int, Int) -> List' Int
between3 = fromCoCh . ListCoCh betweenCoCh
{-# INLINE between3 #-}
\end{code}
\paragraph{Filter}
The filter function is, again, implemented in three different ways:
In a non-encoded fashion, using a church-encoding, and using a cochurch-encoding.
The non-encoded function simply uses recursion:
\begin{code}
filter1 :: (a -> Bool) -> List' a -> List' a
filter1 _ Nil = Nil
filter1 p (Cons x xs) = if p x then Cons x (filter1 p xs) else filter1 p xs
{-# INLINE filter1 #-}
\end{code}
The church-encoded version does \textbf{not} leverage an algebra, as is normally done for natural transformations, but instead something else. I.e. the function \tt{a} below is only selectively applied to the resultant subterms (see the \tt{else} case specifically):
\begin{code}
filterCh :: (a -> Bool) -> ListCh a -> ListCh a
filterCh p (ListCh g) = ListCh (\a -> g (\case
    Nil_ -> a Nil_
    Cons_ x xs -> if (p x) then a (Cons_ x xs) else xs
  ))
filter2 :: (a -> Bool) -> List' a -> List' a
filter2 p = fromCh . filterCh p . toCh
{-# INLINE filter2 #-}
\end{code}
For the cochurch-encoding, a natural transformation can be defined, but it is not a simple algebra, instead it is a recursive function.
There is existing work, called joint-point optimization that should enable this function to still fully fuse, but it does not at the moment, there are existing issues in GHC's issue tracker that describe this problem:
\begin{code}
filt p h s = go s
  where go s = case h s of
          Nil_ -> Nil_
          Cons_ x xs -> if p x then Cons_ x xs else go xs
filterCoCh :: (a -> Bool) -> ListCoCh a -> ListCoCh a
filterCoCh p (ListCoCh h s) = ListCoCh (filt p h) s
filter3 :: (a -> Bool) -> List' a -> List' a
filter3 p = fromCoCh . filterCoCh p . toCoCh
{-# INLINE filter3 #-}
\end{code}
It is possible to implement filter using a natural transformation, but this requires us to modify the type of the base functor, so we can communicate `skip' to the datatype, which our corecursion principle can handle accordingly.
This technique is called \textit{stream fusion} and is described by \cite{Coutts2007}.
\paragraph{Map}
Contrary to filter, it is possible to implement the map function as a natural transformation. Again three implementations, the latter two of which leverage the defined natural transformation \tt{m}:
\begin{code}
map1 :: (a -> b) -> List' a -> List' b
map1 _ Nil = Nil
map1 f (Cons x xs) = Cons (f x) (map1 f xs)
{-# INLINE map1 #-}
m :: (a -> b) -> List_ a c -> List_ b c
m f (Cons_ x xs) = Cons_ (f x) xs
m _ Nil_ = Nil_
map2 :: (a -> b) -> List' a -> List' b
map2 f = fromCh . natCh (m f) . toCh
{-# INLINE map2 #-}
map3 :: (a -> b) -> List' a -> List' b
map3 f = fromCoCh . natCoCh (m f) . toCoCh
{-# INLINE map3 #-}
\end{code}
\paragraph{Sum}
We define our sum function in, \textit{again} three different ways:
non-encoded, church-encoded, and cochurch-encoded.
The non-encoded leverages simple recursion:
\begin{code}
sum1 :: List' Int -> Int
sum1 Nil = 0
sum1 (Cons x xs) = x + sum1 xs
{-# INLINE sum1 #-}
\end{code}
The church-encoded function leverages an algebra and applies that the existing recursion principle:
\begin{code}
su :: List_ Int Int -> Int
su Nil_ = 0
su (Cons_ x y) = x + y
sumCh :: ListCh Int -> Int
sumCh (ListCh g) = g su
sum2 :: List' Int -> Int
sum2 = sumCh . toCh
{-# INLINE sum2 #-}
\end{code}
The cochurch-encoded function implements a corecursion principle and applies the existing coalgebra (and input) to it:
\begin{code}
{-TAIL RECURSION!!!-}
su' :: (s -> List_ Int s) -> s -> Int
su' h s = loopt s 0
  where loop s' = case h s' of
          Nil_ -> 0
          Cons_ x xs -> x + loop xs
        loopt s' sum = case h s' of
          Nil_ -> sum
          Cons_ x xs -> loopt xs (x + sum)
sumCoCh :: ListCoCh Int -> Int
sumCoCh (ListCoCh h s) = su' h s
sum3 :: List' Int -> Int
sum3 = sumCoCh . toCoCh
{-# INLINE sum3 #-}
\end{code}
Note that two subfunctions are provided to \tt{su'}, the \tt{loop} and the \tt{loopt} function.
The former function is implement as one would naively expect.
The latter, interestingly, is implemented using tail-recursion.
Because this \tt{loopt} function constitutes a corecursion principle, all the algebras (or natural transformations) applied to it, will be inlined in such a way that the resultant function is also tail recursive, in some cases providing a significant speedup!
For more details, see the discussion in \autoref{sec:tail}.

\paragraph{Pipelines and GHC list fusion}
\begin{code}
trodd :: Int -> Bool
trodd n = n `rem` 2 == 0
{-# INLINE trodd #-}


pipeline1 = sum1 . map1 (+2) . filter1 trodd . between1
pipeline2 = sum2 . map2 (+2) . filter2 trodd . between2
pipeline3 = sum3 . map3 (+2) . filter3 trodd . between3
pipeline4 (x, y) = loop x y 0
  where loop z y sum = case z > y of
                     True -> sum
                     False -> if trodd z
                              then loop (z+1) y (sum+z+2)
                              else loop (z+1) y sum

between5 :: (Int, Int) -> [Int]
between5 (x, y) = [x..y]
{-# INLINE between5 #-}
filter5 :: (Int -> Bool) -> [Int] -> [Int]
filter5 f xs = build (\c n -> foldr (\a b -> if f a then c a b else b) n xs)
{-# INLINE filter5 #-}
map5 :: forall a b . (a -> b) -> [a] -> [b]
map5 f xs = build (\c n -> foldr (\a b -> c (f a) b) n xs)
{-# INLINE map5 #-}
sum5 :: [Int] -> Int
sum5 = foldl' (\a b -> a+b) 0
{-# INLINE sum5 #-}
pipeline5 = sum5 . map5 (+2) . filter5 trodd . between5

input :: (Int, Int)
input = (1, 10000)
main :: IO ()
main = print (pipeline5 input)
\end{code}
\ignore{
-- sumApp1 (x, y)  = sum1 (append1 (between1 (x, y)) (between1 (x, y)))
-- sumApp2 (x, y)  = sum2 (append2 (between2 (x, y)) (between2 (x, y)))
-- sumApp3 (x, y)  = sum3 (append3 (between3 (x, y)) (between3 (x, y)))

\begin{code}
{-
main :: IO ()
main = defaultMain
  [
    bgroup "Filter pipeline"
    [ 
      bench "piplistfused1" $ nf pipeline5 input
    , bench "piplistfused2" $ nf pipeline5 input
    , bench "piphandfused1" $ nf pipeline4 input
    , bench "piphandfused2" $ nf pipeline4 input
    -- , bench "piphandfused3" $ nf pipeline4 input
    -- , bench "piphandfused4" $ nf pipeline4 input
    , bench "pipcofused1" $ nf pipeline3 input
    , bench "pipcofused2" $ nf pipeline3 input
    -- , bench "pipcofused3" $ nf pipeline3 input
    -- , bench "pipcofused4" $ nf pipeline3 input
    , bench "pipchfused1" $ nf pipeline2 input
    , bench "pipchfused2" $ nf pipeline2 input
    -- , bench "pipchfused3" $ nf pipeline2 input
    -- , bench "pipchfused4" $ nf pipeline2 input
    , bench "pipunfused1" $ nf pipeline1 input
    , bench "pipunfused2" $ nf pipeline1 input
    -- , bench "pipunfused3" $ nf pipeline1 input
    -- , bench "pipunfused4" $ nf pipeline1 input
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
-}
{- Report on core representation analysis for List datatypes,
 - In the core fused representation, lists are completely absent
   for both fused and cofused pipeline
 - The cofused function ends up pulling ahead slightly, not sure why.
   There could be two possible reasons for this:
   - When compiling with tastybench, the fused pipeline is not occupied
     with "unpacking" and "repacking" the first input integer. This difference
     is not present in the core representation without tastybench and just a simple print.
   - In the recursive call there is a lambda present in the body of the case, while in the cofused
     version it is just a DEFAULT declaration, returning the sum of some value.
 - For both there is further optimization possible removing some overhead:
   Passing around the 'y' of the tuple.  This is the case for both fused and cofused.
 - Furthremore, after implementing a 'hand-fused' version of the pipeline,
   it was discovered that it performed identically to the cofused implementation.
   - This 'hand fused' pipeline was then further optimized using tail recursion.
     This turned out to give another 40% speedup, a bummer when compared to cofusion
   - However, with a small change in the definition of the 'final' function of the cofused pipeline,
     su', such that it is also tail recursive gave an identical speedup to the cofused pipeline.
   - One interesting thing of note is that the Core representation of the cofused tai-recursive
     function does not make use of gotos like the hand-written one does. It does, however, seem
     to have identical performance.
   - An analogous change for the church-fused pipeline seems more difficult...
    -}
{- pipeline 3 Rec { 
$wloop :: Int# -> Int# -> Int#
$wloop
  = \ (ww :: Int#) (ww1 :: Int#) ->
      case ># ww ww1 of {
        __DEFAULT ->
          case remInt# ww 3# of wild {
            __DEFAULT ->
              case +# wild (andI# (-# 0# (andI# (<# ww 0#) 1#)) 3#) of {
                __DEFAULT -> $wloop (+# ww 1#) ww1;
                0# ->
                  case $wloop (+# ww 1#) ww1 of ww2 { __DEFAULT ->
                  +# 2# (+# ww2 ww)
                  }
              };
            0# ->
              case $wloop (+# ww 1#) ww1 of ww2 { __DEFAULT ->
              +# 2# (+# ww2 ww)
              }
          };
        1# -> 0#
      }
end Rec }
-}
{- pipeline2 Rec {
main_$s$wb :: Int# -> Int# -> Int
main_$s$wb
  = \ (sc :: Int#) (ww :: Int#) ->
      case ># sc ww of {
        __DEFAULT ->
          case remInt# sc 3# of wild {
            __DEFAULT ->
              case +# wild (andI# (-# 0# (andI# (<# sc 0#) 1#)) 3#) of {
                __DEFAULT -> main_$s$wb (+# sc 1#) ww;
                0# ->
                  case main_$s$wb (+# sc 1#) ww of { I# y -> I# (+# 2# (+# y sc)) }
              };
            0# ->
              case main_$s$wb (+# sc 1#) ww of { I# y -> I# (+# 2# (+# y sc)) }
          };
        1# -> lvl
      }
end Rec }
-}


{- Compile with tastybench -}
{- Cofused
Rec {
$wloop :: Int# -> Int# -> Int#
$wloop
  = \ (ww :: Int#) (ww1 :: Int#) ->
      case ># ww ww1 of {
        __DEFAULT ->
          case remInt# ww 3# of wild {
            __DEFAULT ->
              case +# wild (andI# (-# 0# (andI# (<# ww 0#) 1#)) 3#) of {
                __DEFAULT -> $wloop (+# ww 1#) ww1;
                0# ->
                  case $wloop (+# ww 1#) ww1 of ww2 { __DEFAULT ->
                  +# 2# (+# ww2 ww)
                  }
              };
            0# ->
              case $wloop (+# ww 1#) ww1 of ww2 { __DEFAULT ->
              +# 2# (+# ww2 ww)
              }
          };
        1# -> 0#
      }
end Rec }
 -}
 {- fused
Rec {
$s$wb :: Int -> Int# -> Int
$s$wb
  = \ (ww :: Int) (ww1 :: Int#) ->
      case ww of { I# x ->
      case ># x ww1 of {
        __DEFAULT ->
          case remInt# x 3# of wild1 {
            __DEFAULT ->
              case +# wild1 (andI# (-# 0# (andI# (<# x 0#) 1#)) 3#) of {
                __DEFAULT -> $s$wb (I# (+# x 1#)) ww1;
                0# ->
                  case $s$wb (I# (+# x 1#)) ww1 of { I# y -> I# (+# 2# (+# y x)) }
              };
            0# ->
              case $s$wb (I# (+# x 1#)) ww1 of { I# y -> I# (+# 2# (+# y x)) }
          };
        1# -> lvl
      }
      }
end Rec } 
 -}








{-
Chfused
Rec {
$s$wb :: Int -> Int# -> Int
$s$wb
  = \ (ww :: Int) (ww1 :: Int#) ->
      case ww of { I# x ->
      case ># x ww1 of {
        __DEFAULT ->
          case remInt# x 2# of {
            __DEFAULT -> $s$wb (I# (+# x 1#)) ww1;
            0# ->
              case $s$wb (I# (+# x 1#)) ww1 of { I# y -> I# (+# 2# (+# y x)) }
          };
        1# -> lvl
      }
      }
end Rec }

Rec {
$wloop :: Int# -> Int# -> Int#
$wloop
  = \ (ww :: Int#) (ww1 :: Int#) ->
      case ># ww ww1 of {
        __DEFAULT ->
          case remInt# ww 2# of {
            __DEFAULT -> $wloop (+# ww 1#) ww1;
            0# ->
              case $wloop (+# ww 1#) ww1 of ww2 { __DEFAULT ->
              +# 2# (+# ww2 ww)
              }
          };
        1# -> 0#
      }
end Rec }
-}
\end{code}
}