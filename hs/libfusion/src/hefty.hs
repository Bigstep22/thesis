{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}

import Prelude hiding (sum)
import Data.Either

infixr 6 +
data (f + g) e = L (f e) | R (g e) deriving (Functor, Show)

infixr 5 <
-- class f < g where forephism :: f k -> g k
-- instance Functor f => f < f where inj = id
-- instance (Functor f , Functor g) => f < (f + g) where inj = L
-- instance {-# Overlappable #-} (Functor f , Functor g, Functor h, f < g) => f < (h + g) where
--   inj = R . inj
inject :: (Functor f, Functor g, g < f) => g (Free f a) -> Free f a
inject = Op . inj

data Free f a = Pure a | Op (f (Free f a))
instance Functor f => Monad (Free f) where
  m >>= k = fold k Op m
instance Functor f => Functor (Free f) where
  fmap f = fold (pure . f) Op
instance Functor f => Applicative (Free f) where
  pure = Pure
  f <*> m = fold (flip fmap m) Op f

fold :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
fold gen _   (Pure x) = gen x
fold gen alg (Op f)   = alg (fmap (fold gen alg) f)

data Handler f a f' b
  = Handler { ret  :: a -> Free f' b
            , hdlr :: f (Free f' b) -> Free f' b }

handle :: (Functor f, Functor f')
       => Handler f a f' b -> Free (f + f') a -> Free f' b
handle h = fold
  (ret h)
  (\x -> case x of
     L y -> hdlr h y
     R y -> Op y)

data End k deriving Functor
data State s k
  = Put s k
  | Get (s -> k)
  deriving Functor
data Err k = Err String deriving Functor

incerr :: Free (Err + State Int + End) a
incerr = do (s :: Int) <- get; put (s + 1); err "foo"

get :: State s < f => Free f s
get = inject (Get Pure)
put  :: State s < f => s -> Free f ()
put s = inject (Put s (Pure ()))
err :: Err < f => String -> Free f a
err msg = inject (Err msg)


hErr :: Functor f' => Handler Err a f' (Either String a)
hErr = Handler
  { ret = pure . Right
  , hdlr = \x -> case x of Err s -> pure (Left s) }



data Handler_ f a p f' b
  = Handler_ { ret_  :: a -> (p -> Free f' b)
             , hdlr_ :: f (p -> Free f' b) -> (p -> Free f' b) }

handle_ :: (Functor f, Functor f')
        => Handler_ f a p f' b -> Free (f + f') a
        -> p -> Free f' b
handle_ h = fold
  (ret_ h)
  (\x -> case x of
     L x -> hdlr_ h x
     R x -> \p -> Op (fmap (\m -> m p) x))
hState :: Functor g => Handler_ (State s) a s g (a, s)
hState = Handler_
  { ret_ = \x s -> pure (x, s)
  , hdlr_ = \x s -> case x of
      Put s' k -> k s'
      Get k -> k s s }

un :: Free End a -> a
un (Pure x) = x
un (Op f) = case f of

res :: Int -> (Either String a, Int)
res x = un (handle_ hState (handle hErr incerr) x)

-- main = print $ snd (res 0)







infixr 5 :->
type (f :-> g) = forall a. f a -> g a
data f <-> g = Iso { to :: f :-> g, from :: g :-> f }

sum :: (f a -> b) -> (g a -> b) -> (f + g) a -> b
sum f _ (L x) = f x
sum _ g (R x) = g x

isoRefl :: f <-> f
isoRefl = Iso id id

isoSym :: f <-> g -> g <-> f
isoSym i = Iso (from i) (to i)

isoTrans :: f <-> g -> g <-> h -> f <-> h
isoTrans i1 i2 = Iso (to i2 . to i1) (from i1 . from i2)

isoSumCong :: f <-> f' -> g <-> g' -> (f + g) <-> (f' + g')
isoSumCong i1 i2 = Iso
  (sum (L . to i1) (R . to i2))
  (sum (L . from i1) (R . from i2))

isoSumComm :: (f + g) <-> (g + f)
isoSumComm = Iso
  (sum R L)
  (sum R L)

isoSumAssoc :: (f + (g + h)) <-> ((f + g) + h)
isoSumAssoc = Iso
  (sum (L . L) (sum (L . R) R))
  (sum (sum L (R . L)) (R . R))

data Forephism f g
  = forall f'. (Functor g, Functor f, Functor f') =>
      Forephism { iso :: g <-> (f + f') }
class (Functor f, Functor g) => f < g where
  forephism :: Forephism f g
instance Functor f => f < f where
  forephism = Forephism (Iso
    L
    (sum id (\(x :: End a) -> case x of)))
instance (Functor f, Functor g) => f < f + g where
  forephism = Forephism isoRefl
instance {-# Overlappable #-} (Functor f , Functor g, Functor h, f < g)
      => f < (h + g) where
  forephism = case forephism of
    Forephism i -> Forephism
      (isoTrans
         (isoSumCong isoRefl i)
         (isoTrans isoSumComm (isoSym isoSumAssoc)))

mask :: Functor f => Free f a -> Free (f' + f) a
mask = fold Pure (Op . R)


permute :: (Functor f, Functor f')
        => (f :-> f') -> Free f a -> Free f' a
permute f = fold Pure (Op . f)

hup :: f < g => (forall f'. Functor f' => Free (f + f') a -> Free f' b)
    -> Free g a -> Free g b
hup h = case forephism of
  Forephism i -> permute (from i) . mask . h . permute (to i)



inj :: f < g => f a -> g a
inj = case forephism of
  Forephism i -> from i . L












class (forall f. Functor (h f)) => HOFunctor h where
  hmap :: (f :-> g) -> (h f :-> h g)
infixr 6 :<
class (HOFunctor sub, HOFunctor sup) => sub :< sup where
  hoinj :: sub a :-> sup a
infixr 6 :+
data (h1 :+ h2) (m :: * -> *) k = HL (h1 m k) | HR (h2 m k)
  deriving Functor
instance (HOFunctor h1, HOFunctor h2) => HOFunctor (h1 :+ h2) where
  hmap f (HL x) = HL (hmap f x)
  hmap f (HR x) = HR (hmap f x)
hoinject :: (HOFunctor f, HOFunctor g, g :< f) => g (Hefty f) (Hefty f a) -> Hefty f a
hoinject = Do . hoinj
instance HOFunctor f => f :< f where hoinj = id
instance (HOFunctor f , HOFunctor g) => f :< (f :+ g) where hoinj = HL
instance {-# Overlappable #-} (HOFunctor f , HOFunctor g, HOFunctor h, f :< g) => f :< (h :+ g) where
  hoinj = HR . hoinj


data Hefty h a = Return a | Do (h (Hefty h) (Hefty h a))
data h :=> g
  = HA { ha :: forall a. h g (g a) -> g a }

hfold :: HOFunctor h
      => (forall a. a -> g a)
      -> h :=> g
      -> (Hefty h :-> g)
hfold gen _   (Return x) = gen x
hfold gen alg (Do x)     =
  ha alg (fmap (hfold gen alg) (hmap (hfold gen alg) x))

data A f (m :: * -> *) k = A (f k) deriving Functor
instance Functor f => HOFunctor (A f) where hmap _ (A x) = A x
a :: (A f :< h, Functor f) => Free f a -> Hefty h a
a = fold Return (hoinject . A)
oa :: A (Output Int) :< h => Free (Output Int) a -> Hefty h a
oa = a
eA :: g < f => A g :=> Free f
eA = HA (\(A x) -> inject x)

data Reader r m k
  = Ask (r -> k)
  | forall a. Local (r -> r) (m a) (a -> k)
deriving instance Functor (Reader r m)
instance HOFunctor (Reader r) where
  hmap _ (Ask k)       = Ask k
  hmap f (Local g m k) = Local g (f m) k
ask :: Reader r :< h => Hefty h r
ask = hoinject (Ask Return)
local :: Reader r :< h => (r -> r) -> Hefty h a -> Hefty h a
local f m = hoinject (Local f m Return)
data AAsk r k = AAsk (r -> k) deriving (Functor)
aask :: (AAsk r < f) => Free f r
aask = inject (AAsk Pure)
hAAsk :: Functor f' => r -> Handler (AAsk r) a f' a
hAAsk r = Handler
  { ret = pure
  , hdlr = \x -> case x of AAsk k -> k r }

instance (Show k) => Show ((->) Int k) where
    show f = show (f 10)

data Output x k = Out x k deriving (Functor, Show)
out :: Output x < f => x -> Free f ()
out x = inject (Out x (Pure ()))

hOut :: Functor f' => Handler (Output x) a f' (a, [x])
hOut = Handler
  { ret = \x -> pure (x, [])
  , hdlr = \x -> case x of
      Out y k -> fmap (\(v,ys) -> (v,y:ys)) k }


infixr 6 /\
(/\) :: h1 :=> g -> h2 :=> g -> (h1 :+ h2) :=> g
a1 /\ a2 = HA (\x -> case x of
  HL x -> ha a1 x
  HR y -> ha a2 y)

eReader :: AAsk r < f => Reader r :=> Free f
eReader = HA (\x -> case x of
  Ask k       -> aask >>= k
  Local f m k -> do
    r <- aask
    hup (handle (hAAsk (f r))) m >>= k)

elaborate :: Hefty (Reader Int :+ A (Output Int) :+ A End) a -> Free (AAsk Int + Output Int + End) a
elaborate = hfold Pure (eReader /\ eA /\ eA)
run :: Hefty (Reader Int :+ A (Output Int) :+ A End) a -> (a, [Int])
run x = un (handle hOut (handle (hAAsk 41) (elaborate x)))

localout :: Hefty (Reader Int :+ A (Output Int) :+ A End) ()
localout = local (+ (1 :: Int)) (do
  (i :: Int) <- ask
  oa (out i))

main = print $ run' localout


eReader' :: State Int < f => Reader Int :=> Free f
eReader' = HA (\x -> case x of
  Ask k       -> get >>= k
  Local f m k -> do
    (i :: Int) <- get
    put (f i)
    v <- m
    put i
    k v)
elaborate' :: Hefty (Reader Int :+ A (Output Int) :+ A End) a -> Free (State Int + Output Int + End) a
elaborate' = hfold Pure (eReader' /\ eA /\ eA)
run' :: Hefty (Reader Int :+ A (Output Int) :+ A End) a -> ((a, Int), [Int])
run' x = un (handle hOut (handle_ hState (elaborate' x) 41))



ffold :: forall h g a b.
         HOFunctor h          -- as hfold
      => (forall c. c -> g c) -- as hfold
      -> h :=> g              -- as hfold
      -> (a -> b)             -- base generator
      -> (h g b -> b)         -- base algebra
      -> Hefty h a
      -> b
ffold _   _ genb _  (Return x) = genb x
ffold gen a genb ab (Do x) = ab         -- 3.
     (hmap (hfold gen a)                -- 2.
       (fmap (ffold gen a genb ab) x))  -- 1.

instance HOFunctor h => Monad (Hefty h) where
  m >>= k = ffold Return (HA Do) k Do m

instance HOFunctor h => Applicative (Hefty h) where
  pure = Return
  f <*> m = ffold Return (HA Do) (flip fmap m) Do f

instance HOFunctor h => Functor (Hefty h) where
  fmap f = ffold Return (HA Do) (pure . f) Do