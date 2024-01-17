{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE InstanceSigs #-}

infixr 6 +
data (f + g) e = L (f e) | R (g e) deriving (Functor, Show)
data Free f a = Pure a | Op (f (Free f a))

instance Functor f => Monad (Free f) where
  (>>=) :: Functor f => Free f a -> (a -> Free f b) -> Free f b
  m >>= k = fold' k Op m
instance Functor f => Functor (Free f) where
  fmap f = fold' (pure . f) Op
instance Functor f => Applicative (Free f) where
  pure = Pure
  f <*> m = fold' (flip fmap m) Op f
fold' :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
fold' gen _   (Pure x) = gen x
fold' gen alg (Op f)   = alg (fmap (fold' gen alg) f)
data Handler f a f' b
  = Handler { ret  :: a -> Free f' b
            , hdlr :: f (Free f' b) -> Free f' b }

handle :: (Functor f, Functor f')
       => Handler f a f' b -> Free (f + f') a -> Free f' b
handle h = fold'
  (ret h)
  (\x -> case x of
     L y -> hdlr h y
     R y -> Op y)

data Free_ f a b = Pure_ a | Op_ (f b)-- deriving Functor
instance Functor f => Applicative (Free_ f a) where
  pure = Pure_
  f <*> m = fold (flip fmap m) Op f
instance Functor f => Functor (Free_ f a) where
  fmap f = fold (pure . f) Op


-- Church encoding of a free monad with conversions
data FreeCh f a = FreeCh (forall b. (Free_ f a b -> b) -> b)

toCh :: Functor f => Free f a -> FreeCh f a
toCh f = FreeCh (`fold` f)

fromCh :: Functor f => FreeCh f a -> Free f a
fromCh (FreeCh fold) = fold ins

fold :: Functor f => (Free_ f a b -> b) -> Free f a -> b
fold a (Pure x) = a (Pure_ x)
fold a (Op fx) = a (Op_ (fmap (fold a) fx))

ins :: Functor f => Free_ f a (Free f a) -> Free f a
ins (Pure_ x) = Pure x
ins (Op_ fx) = Op fx

-- Cochurch encoding of a free monad with conversions
data FreeCoCh f a = forall s. FreeCoCh (s -> Free_ f a s) s

toCoCh :: Functor f => Free f a -> FreeCoCh f a
toCoCh = FreeCoCh outs

fromCoCh :: Functor f => FreeCoCh f a -> Free f a
fromCoCh (FreeCoCh h s) = unfold h s

unfold :: Functor f => (b -> Free_ f a b) -> b -> Free f a
unfold h s = case h s of
  Pure_ x -> Pure x
  Op_ fx -> Op (fmap (unfold h) fx)

outs :: Functor f => Free f a -> Free_ f a (Free f a)
outs (Pure x) = Pure_ x
outs (Op fx) = Op_ fx


main = print "hello, Haskell"






