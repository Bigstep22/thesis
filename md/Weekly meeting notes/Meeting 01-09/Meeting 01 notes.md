Take a look in the std library of Agda, includes some cat. theory.

Take nates during reading, (is difficult), makes the writing process faster. Allows you to pick out the more important details.

deriving: haskell deriving generics. 
Generating newtypes might be a challenge...
Template haskell. https://hackage.haskell.org/package/recursion-schemes-5.2.2.5/docs/Data-Functor-Foldable-TH.html

https://plfa.github.io

Agda: Either emacs or VSCode. VSCode plugin might not work nice with vim keybindings.

Benchmarking tools: tastybench, 
Profiling tools: we want to see how fusion works, dynamic runtime profiling might not be illuminating.
Reading compile-time output: might be more illustrative.
- `-ddump-simpl` : Give a dump
-  `-fforce-recomp` : Force the recompile, might be handle when starting dumps
- `-dno-typeable-binds`: Remove a lot of uneeded information
- `-dsuppress-all`: remove even more information
- `-dsuppress-uniques`: Give nicer shorter names to generated names
- `-dno-suppress-type-signatures` : Handy for adding type signatures
- https://downloads.haskell.org/ghc/latest/docs/users_guide/debugging.html

Meeting every wednesday

I'll make a structure for the meetings. What have I done, what did I run into, what am I going to do, and misc.

What are records:
```
data h :=> g
= HA { ha :: forall a. h g (g a) -> g a }

-- Gets changed to:

data h :=> g
  = HA (forall a. h g (g a) -> g a)

ha :: h :=> g -> forall a. h g (g a) -> g a
ha (HA x) = x

The only thing you lose with this is the ability to do HA {ha = ....}
You can still do (HA ...) syntax
```


Coming week:
Setup Agda environment.
- Follow this path as far as I can go for a week
Implement Free monad fusion and find some benchmarks for it.
Make a Gantt chart! with all of the tasks
Setup Obsidian for note taking while reviewing literature
Give presentation about fusion.