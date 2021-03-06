{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Universes where

open import Agda.Primitive public
  renaming ( Set to Type ; SetÏ to TypeÏ )

-- given some level we can talk about the universe of level ð
-- we put it as a lambda because it's a nameless function
_ : (ð : Level) â Type (lsuc ð)
_ = Î» ð â Type ð

-- these are implicitly generalized variables
variable
  â : Level