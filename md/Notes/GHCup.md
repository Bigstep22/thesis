Haskell compiler management tool.
Allows installation of GHC, HLS, Cabal, and Stack. All with any number of different versions simultaneously, additionally alowing for the installation of a 'primary' version that will used when invoking commands without a version number (e.g. `ghc` will invoke the primary version of ghc that is selected instead of having to write out `ghc-9.4`)

Make sure to set you proper $PATH environment variable in your .bashrc or analagous shell configuration file:
`export PATH="$HOME/.cabal/bin:$HOME/.ghcup/bin:$PATH"`
- https://wiki.archlinux.org/title/Haskell#ghcup

This managed to solve the versioning difficulties I had with Haskell. Don't use Arch's ghc and package management system.