Feedback article:
- Motivate why my contributions are important
- Slim down Fusion part of introduction, move rest to a related works section right before conclusion.

About Natural transformation:
- The naturality condition is strict, but provides theoretical cleanliness
	- But, in Haskell you can write it as a non-natural transformation, at the cost of needing join points, etc.
- See below code for base functor of Free monad:
```
data Free f a = Pure a | Free (f (Free f a))

data Mu f = In (f (Mu f))

IH: Mu (Const a :+: f) = Free f a

In ((Const a :+: f) (Mu (Const a :+: f)))
In1 (Const a (Mu ...)) | In2 (f (Mu (Const a :+: f)))
In1 a | In2 (f (Mu (Const a :+: f)))
Pure a | Free (f (Mu (Const a :+: f)))
Pure a | Free (f (Free f a))
```