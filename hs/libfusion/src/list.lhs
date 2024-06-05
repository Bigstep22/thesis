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
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -O2 #-}
import Prelude hiding (foldr, concatMap)
import Test.Tasty.Bench
import GHC.Base
\end{code}
}
\subsection{Lists}
In this section further replication of \cite{Harper2011}'s work is described, but Lists are implemented instead of Leaf trees.

This was done to see how the descriptions in \cite{Harper2011}'s work generalize and to have a simpler datastructure on which to perform analysis; seeing how and when the fusion works and when it doesn't.

We again start with the datatype descriptions. We use \tt{List'} instead of \tt{List} as there is a namespace collision with GHC's \tt{List} datatype:
\begin{code}
import GHC.List
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
\end{code}
We introduce three important pragmas.
One is the actual fusion rule, taking two functions and removing them from the compilation process.
The second and third are to make sure that the \tt{toCh} and \tt{fromCh} functions are inlined as late as possible; maximising the time that they can be fused during the compilation process:
\begin{code}
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
The cochurch encodings are defined similarly, including pragmas necessary for fusion:
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
b a (x, y) = loop x
  where loop x = case x > y of
          True -> a Nil_
          False -> a (Cons_ x (loop (x+1)))
betweenCh :: (Int, Int) -> ListCh Int
betweenCh (x, y) = ListCh (\a -> b a (x, y))
{-# INLINE betweenCh #-}
between2 :: (Int, Int) -> List' Int
between2 = fromCh . betweenCh
{-# INLINE between2 #-}
\end{code}
For the Cochurch-encoded version we define a coalgebra:
\begin{code}
betweenCoCh :: (Int, Int) -> List_ Int (Int, Int)
betweenCoCh (x, y) = if x > y 
                     then Nil_
                     else Cons_ x (x+1, y)
{-# INLINE betweenCoCh #-}
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
For the Church and Cochurch encoding see the extended discussion in \autoref{sec:filter_prob}.

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


su2' :: List_ Int (Int -> Int) -> (Int -> Int)
su2' Nil_ s = s
su2' (Cons_ x y) s = y (s + x)
sumCh' :: ListCh Int -> (Int -> Int)
sumCh' (ListCh g) = g su2'
sum7 :: List' Int -> Int
sum7 = flip sumCh' 0 . toCh
{-# INLINE sum7 #-}


\end{code}
The cochurch-encoded function implements a corecursion principle and applies the existing coalgebra (and input) to it:
\begin{code}
{-TAIL RECURSION!!!-}
su2 :: (s -> List_ Int s) -> s -> Int
su2 h s = loopt s 0
  where loopt s' sum = case h s' of
          Nil_ -> sum
          Cons_ x xs -> loopt xs (x + sum)
su3 :: (s -> List_ Int s) -> s -> Int
su3 h s = loop s
  where loop s' = case h s' of
          Nil_ -> 0
          Cons_ x xs -> x + loop xs
sumCoCh :: ListCoCh Int -> Int
sumCoCh (ListCoCh h s) = su2 h s
sumCoCh2' :: ListCoCh Int -> Int
sumCoCh2' (ListCoCh h s) = su3 h s
sum3 :: List' Int -> Int
sum3 = sumCoCh . toCoCh
{-# INLINE sum3 #-}
sum8 :: List' Int -> Int
sum8 = sumCoCh . toCoCh
{-# INLINE sum8 #-}
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
pipeline7 = sum7 . map2 (+2) . filter2 trodd . between2
pipeline3 = sum3 . map3 (+2) . filter3 trodd . between3
pipeline8 = sum8 . map3 (+2) . filter3 trodd . between3
pipeline4 (x, y) = loop x 0
  where loop z sum = if z > y 
                     then sum
                     else if trodd z
                          then loop (z+1) (sum+z+2)
                          else loop (z+1) sum

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
pipeline6 = sum6 . map6 (+2) . filter6 trodd . between6
pipeline9 = sum9 . map6 (+2) . filter6 trodd . between6
pipeline10 = sum10 . map10 (+2) . filter10 trodd . between10
pipeline11 = sum11 . map10 (+2) . filter10 trodd . between10
\end{code}







\subsubsection{The Filter Problem}\label{sec:filter_prob}
% What is the difference between an algeabra, coalgebra, transformation, and natural transformation?
I have moved the discussion for Church and Cochurch encoded Lists down here, as I think it warrants more discussion and illustrates a few interesting points.
There are multiple ways of implementing it, none of them trivial according to \cite{Harper2011}'s description of how it should be implemented as a natural transformation.

When replicating \cite{Harper2011}'s code for lists, there is one major limitation on natrual transformation functions:
How to represent filter as a natural transformation for both Church and Cochurch encodings?
In his work he implemented, using Leaf trees, a natural transformation for the filter function in the following manner:
\begin{spec}
filt :: (a -> Bool) -> Tree_ a c -> Tree_ a c
filt p Empty_ = Empty_
filt p (Leaf_ x) = if p x then Leaf_ x else Empty_
filt p (Fork_ l r) = Fork_ l r
filter2 :: (a -> Bool) -> Tree a -> Tree a
filter2 p = fromCh . natCh (filt p) . toCh
filter3 :: (a -> Bool) -> Tree a -> Tree a
filter3 p = fromCoCh . natCoCh (filt p) . toCoCh
\end{spec}
This \tt{filt} function was then subsequently used in the Church and Cochurch encoded function.
Let's try this for the \tt{List} datatype:
\begin{spec}
filt :: (a -> Bool) -> List_ a c -> List_ a c
filt p Nil_ = Nil_
filt p (Cons_ x xs) = if p x then Cons_ x xs else ? 
\end{spec}
The question is, what should be in the place of the \tt{?} above?
Initially you might say \tt{xs}, as the \tt{Cons\_ x} part should be filtered away, and this would be conceptually correct except for the fact that \tt{xs} is of type \tt{c}, and not of type \tt{List\_ a c}.
Filling in \tt{xs} gives a type error.
Let's change the type annotation then, right?
Well no, if we did that we wouldn't have the type of a transformation anymore, so we can't do that either.

There are two solutions:
One that modifies the definition of \tt{filter2} and \tt{filter3}, such that the definition is still possible, without leveraging transformations.
The other modifies the definition of the underlying type such that the filter function is still possible to express as a transformation.
    
\paragraph{Solution 1: Abandoning Natural Transformations}
\subparagraph{Church}
Whereas before we wanted to implement our \tt{filter} function in the following manner:
\begin{spec}
filterCh :: (forall c . List_ a c -> List_ b c) -> ListCh a -> ListCh b
filterCh p (ListCh g) = ListCh (\a -> g (a . (filt p)))
filter2 :: (a -> Bool) -> List a -> List a
filter2 p = fromCh . filterCh p . toCh
\end{spec}
We now need to modify the \tt{filterCh} function such that we can still express a filter function \textit{witout} using a natural transformation:
\begin{spec}
filterCh :: (forall c . List_ a c -> List_ b c) -> ListCh a -> ListCh b
filterCh p (ListCh g) = ListCh (\a -> g ?)
\end{spec}
Replacing the \tt{?} above such that we apply the \tt{a} selectively we can yield:
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
Notice how we do not apply \tt{a} to \tt{xs}, and, in doing so, can put \tt{xs} in the place where wanted to.
The definition of \tt{filterCh} was too restrictive in always postcomposing \tt{a}.

The astute observer will note that this solution is just a beta reduced form of a build/foldr composition pair!
% TODO: Write out a build/foldr pair and beta reduce it
% Is it a build/foldr pair? There is no recursion...
% Something like a half-algebra...

% I was just reading this: https://link.springer.com/chapter/10.1007/978-3-540-30477-7_22
% This is one of the fusion rules that is leveraged in GHC.List fusion.
% Interesting read.


\subparagraph{Cochurch}
Whereas before we wanted to implement our \tt{filter} function in the following manner:
\begin{spec}
filter3 :: (a -> Bool) -> List a -> List a
filter3 p = fromCoCh . natCoCh (filt p) . toCoCh
\end{spec}
For the cochurch-encoding, a natural transformation can be defined, but it is not a simple algebra, instead it is a recursive function.\footnote{And not necessarily guaranteed to terminate, the seed could generate an infinite structure.}
The core idea is: we combine the natural transformation and postcomposition again, but this time we make the function recursively grab elements from the seed until we find one that satisfies the predicate.
\begin{code}
filt :: (a -> Bool) -> (s -> List_ a s) -> s -> List_ a s
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
The \tt{go} subfunction is recursive, so it does not inline (fuse) neatly into the main function body in the way that the rest of the pipeline does.
There is existing work, called join-point optimization that should enable this function to still fully fuse, but it does not at the moment.
There are existing issues in GHC's issue tracker that describe this problem.\footnote{\url{https://gitlab.haskell.org/ghc/ghc/-/issues/22227}}


\paragraph{Solution 2: go back and modify the underlying type}
It is possible to implement filter using a natural transformation, but this requires us to modify the type of the base functor.
We can add a new constructor to the datatype that allows us to null out the value of our datatype: \tt{ConsN'\_ xs}.
This way we can write the \tt{filt} function in the following fashion:
\begin{code}
filt' :: (a -> Bool) -> List'_ a c -> List'_ a c
filt' p Nil'_ = Nil'_
filt' p (ConsN'_ xs) = ConsN'_ xs
filt' p (Cons'_ x xs) = if p x then Cons'_ x xs else ConsN'_ xs
\end{code}
Now we do need to modify all of our already defined functions to take into account this modified datatype.
The astute among you might notice that this technique is actually \textit{stream fusion} as described by \cite{Coutts2007}.
The \tt{ConsN\_} constructor is analogous to the \tt{Skip} constructor.
Therefore, this is a known and understood technique, motivated by the limitations of the techniques described by Harper.

So why was it possible to implement \tt{filt} without modifying the datatype of leaf trees?
Because leaf trees already have this consideration of being able to null the datatype in-place by chaining a \tt{Leaf\_ x} into an \tt{Empty\_}.
\tt{filt} is able to remove a value from the datastructure without changing the structure of the data. I.e. it is still a natural transformation.
By chaning the list datatype such that this nullability is also possible, we can also write \tt{filt} as a natural transformation.

This technique could be broader than a modification to just lists.
By modifying (making nullable) any datatype, it might be possible to broaden the class of functions that can be represented as a natural transformation.
One other example of this is already the difference between a \tt{Binary Tree} and a \tt{Leaf Tree} datatype:
\begin{spec}
data BinTree a = Leaf a | Fork (BinTree a) (BinTree a)
data LeafTree a = Empty | Leaf a | Fork (LeafTree a) (LeafTree a)
\end{spec}
The \tt{Leaf} constructor of \tt{BinTree} is also made nullable.
I will leave the following question to future work: Is this generalizable?






\ignore{
\begin{code}
data List'_ a b = Nil'_ | Cons'_ a b | ConsN'_ b
data ListCoCh' a = forall s . ListCoCh' (s -> List'_ a s) s
toCoCh' :: List' a -> ListCoCh' a
toCoCh' = ListCoCh' out'
out' :: List' a -> List'_ a (List' a)
out' Nil = Nil'_
out' (Cons x xs) = Cons'_ x xs
fromCoCh' :: ListCoCh' a -> List' a
fromCoCh' (ListCoCh' h s) = unfold' h s
unfold' :: (b -> List'_ a b) -> b -> List' a
unfold' h s = case h s of
  Nil'_ -> Nil
  ConsN'_ xs -> unfold' h xs
  Cons'_ x xs -> Cons x (unfold' h xs)
{-# RULES "toCh/fromCh fusion"
   forall x. toCoCh' (fromCoCh' x) = x #-}
{-# INLINE [0] toCoCh' #-}
{-# INLINE [0] fromCoCh' #-} 
betweenCoCh' :: (Int, Int) -> List'_ Int (Int, Int)
betweenCoCh' (x, y) = if (x > y)
                      then Nil'_
                      else Cons'_ x (x+1, y)
{-# INLINE betweenCoCh' #-}
between6 :: (Int, Int) -> List' Int
between6 = fromCoCh' . ListCoCh' betweenCoCh'
{-# INLINE between6 #-}
natCoCh' :: (forall c . List'_ a c -> List'_ b c) -> ListCoCh' a -> ListCoCh' b
natCoCh' f (ListCoCh' h s) = ListCoCh' (f . h) s
m' :: (a -> b) -> List'_ a c -> List'_ b c
m' f (Cons'_ x xs) = Cons'_ (f x) xs
m' _ (ConsN'_ xs) = ConsN'_ xs
m' _ Nil'_ = Nil'_
map6 :: (a -> b) -> List' a -> List' b
map6 f = fromCoCh' . natCoCh' (m' f) . toCoCh'
{-# INLINE map6 #-}
filter6 :: (a -> Bool) -> List' a -> List' a
filter6 p = fromCoCh' . natCoCh' (filt' p) . toCoCh'
{-# INLINE filter6 #-}
su' :: (s -> List'_ Int s) -> s -> Int
su' h s = loopt 0 s
  where loopt sum s' = case h s' of
          Nil'_ -> sum
          ConsN'_ xs -> loopt sum xs
          Cons'_ x xs -> loopt (x + sum) xs
su3' :: (s -> List'_ Int s) -> s -> Int
su3' h s = loop s
  where loop s' = case h s' of
          Nil'_ -> 0
          ConsN'_ xs -> loop xs
          Cons'_ x xs -> x + loop xs
sumCoCh' :: ListCoCh' Int -> Int
sumCoCh' (ListCoCh' h s) = su' h s
sumCoCh3' :: ListCoCh' Int -> Int
sumCoCh3' (ListCoCh' h s) = su3' h s
sum6 :: List' Int -> Int
sum6 = sumCoCh' . toCoCh'
{-# INLINE sum6 #-}
sum9 :: List' Int -> Int
sum9 = sumCoCh3' . toCoCh'
{-# INLINE sum9 #-}





data ListCh' a = ListCh' (forall b . (List'_ a b -> b) -> b)
toCh' :: List' a -> ListCh' a
toCh' t = ListCh' (\a -> fold' a t)
fold' :: (List'_ a b -> b) -> List' a -> b
fold' a Nil         = a Nil'_
fold' a (Cons x xs) = a (Cons'_ x (fold' a xs))
fromCh' :: ListCh' a -> List' a
fromCh' (ListCh' fold') = fold' in''
in'' :: List'_ a (List' a) -> List' a
in'' Nil'_ = Nil
in'' (ConsN'_ xs) = xs
in'' (Cons'_ x xs) = Cons x xs
{-# RULES "toCh/fromCh fusion"
   forall x. toCh' (fromCh' x) = x #-}
{-# INLINE [0] toCh' #-}
{-# INLINE [0] fromCh' #-}
natCh' :: (forall c . List'_ a c -> List'_ b c) -> ListCh' a -> ListCh' b
natCh' f (ListCh' g) = ListCh' (\a -> g (a . f))


b'' :: (List'_ Int b -> b) -> (Int, Int) -> b
b'' a (x, y) = loop x
  where loop x = case x > y of
          True -> a Nil'_
          False -> a (Cons'_ x (loop (x+1)))
betweenCh' :: (Int, Int) -> ListCh' Int
betweenCh' (x, y) = ListCh' (\a -> b'' a (x, y))
{-# INLINE betweenCh' #-}
between10 :: (Int, Int) -> List' Int
between10 = fromCh' . betweenCh'
{-# INLINE between10 #-}
map10 :: (a -> b) -> List' a -> List' b
map10 f = fromCh' . natCh' (m' f) . toCh'
{-# INLINE map10 #-}
filter10 :: (a -> Bool) -> List' a -> List' a
filter10 p = fromCh' . natCh' (filt' p) . toCh'
{-# INLINE filter10 #-}
su''' :: List'_ Int Int -> Int
su''' Nil'_ = 0
su''' (ConsN'_ y) = y
su''' (Cons'_ x y) = x + y
sumCh'' :: ListCh' Int -> Int
sumCh'' (ListCh' g) = g su'''
sum10 :: List' Int -> Int
sum10 = sumCh'' . toCh'
{-# INLINE sum10 #-}
su2'' :: List'_ Int (Int -> Int) -> (Int -> Int)
su2'' Nil'_ = oneShot (\s -> s)
su2'' (ConsN'_ y) = oneShot (\s -> y s)
su2'' (Cons'_ x y) = oneShot (\s -> y (s + x))
sumCh''' :: ListCh' Int -> (Int -> Int)
sumCh''' (ListCh' g) = g su2''
sum11 :: List' Int -> Int
sum11 = flip sumCh''' 0 . toCh'
{-# INLINE sum11 #-}


-- sumApp1 (x, y)  = sum1 (append1 (between1 (x, y)) (between1 (x, y)))
-- sumApp2 (x, y)  = sum2 (append2 (between2 (x, y)) (between2 (x, y)))
-- sumApp3 (x, y)  = sum3 (append3 (between3 (x, y)) (between3 (x, y)))


input :: (Int, Int)
input = (1, 10000)
-- main :: IO ()
-- main = print (pipeline5 input)
makegroup n = [ 
      bench "pipunfused1" $ nf pipeline1 (1, n)
    , bench "pipunfused2" $ nf pipeline1 (1, n)
    , bench "pipunfused3" $ nf pipeline1 (1, n)
    , bench "pipunfused4" $ nf pipeline1 (1, n)
    , bench "pipunfused5" $ nf pipeline1 (1, n)
    , bench "pipchfused1" $ nf pipeline2 (1, n)
    , bench "pipchfused2" $ nf pipeline2 (1, n)
    , bench "pipchfused3" $ nf pipeline2 (1, n)
    , bench "pipchfused4" $ nf pipeline2 (1, n)
    , bench "pipchfused5" $ nf pipeline2 (1, n)
    , bench "pipchtailfused1" $ nf pipeline7 (1, n)
    , bench "pipchtailfused2" $ nf pipeline7 (1, n)
    , bench "pipchtailfused3" $ nf pipeline7 (1, n)
    , bench "pipchtailfused4" $ nf pipeline7 (1, n)
    , bench "pipchtailfused5" $ nf pipeline7 (1, n)
    , bench "pipchstreamfused1" $ nf pipeline10 (1, n)
    , bench "pipchstreamfused2" $ nf pipeline10 (1, n)
    , bench "pipchstreamfused3" $ nf pipeline10 (1, n)
    , bench "pipchstreamfused4" $ nf pipeline10 (1, n)
    , bench "pipchstreamfused5" $ nf pipeline10 (1, n)
    , bench "pipchstreamtailfused1" $ nf pipeline11 (1, n)
    , bench "pipchstreamtailfused2" $ nf pipeline11 (1, n)
    , bench "pipchstreamtailfused3" $ nf pipeline11 (1, n)
    , bench "pipchstreamtailfused4" $ nf pipeline11 (1, n)
    , bench "pipchstreamtailfused5" $ nf pipeline11 (1, n)
    , bench "pipcofused1" $ nf pipeline8 (1, n)
    , bench "pipcofused2" $ nf pipeline8 (1, n)
    , bench "pipcofused3" $ nf pipeline8 (1, n)
    , bench "pipcofused4" $ nf pipeline8 (1, n)
    , bench "pipcofused5" $ nf pipeline8 (1, n)
    , bench "pipcotailfused1" $ nf pipeline3 (1, n)
    , bench "pipcotailfused2" $ nf pipeline3 (1, n)
    , bench "pipcotailfused3" $ nf pipeline3 (1, n)
    , bench "pipcotailfused4" $ nf pipeline3 (1, n)
    , bench "pipcotailfused5" $ nf pipeline3 (1, n)
    , bench "pipcostreamfused1" $ nf pipeline9 (1, n)
    , bench "pipcostreamfused2" $ nf pipeline9 (1, n)
    , bench "pipcostreamfused3" $ nf pipeline9 (1, n)
    , bench "pipcostreamfused4" $ nf pipeline9 (1, n)
    , bench "pipcostreamfused5" $ nf pipeline9 (1, n)
    , bench "pipcostreamtailfused1" $ nf pipeline6 (1, n)
    , bench "pipcostreamtailfused2" $ nf pipeline6 (1, n)
    , bench "pipcostreamtailfused3" $ nf pipeline6 (1, n)
    , bench "pipcostreamtailfused4" $ nf pipeline6 (1, n)
    , bench "pipcostreamtailfused5" $ nf pipeline6 (1, n)
    , bench "piplistfused1" $ nf pipeline5 (1, n)
    , bench "piplistfused2" $ nf pipeline5 (1, n)
    , bench "piplistfused3" $ nf pipeline5 (1, n)
    , bench "piplistfused4" $ nf pipeline5 (1, n)
    , bench "piplistfused5" $ nf pipeline5 (1, n)
    , bench "piphandfused1" $ nf pipeline4 (1, n)
    , bench "piphandfused2" $ nf pipeline4 (1, n)
    , bench "piphandfused3" $ nf pipeline4 (1, n)
    , bench "piphandfused4" $ nf pipeline4 (1, n)
    , bench "piphandfused5" $ nf pipeline4 (1, n)
    ]
main :: IO ()
main = defaultMain
  [
    bgroup "Filter pipeline 100" (makegroup 100),
    bgroup "Filter pipeline 1000" (makegroup 1000),
    bgroup "Filter pipeline 10000" (makegroup 10000),
    bgroup "Filter pipeline 100000" (makegroup 100000),
    bgroup "Filter pipeline 1000000" (makegroup 1000000),
    bgroup "Filter pipeline 10000000" (makegroup 10000000)
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
