{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Universes where

open import Agda.Primitive public
  renaming ( Set to Type ; Setω to Typeω )

-- given some level we can talk about the universe of level 𝓁
-- we put it as a lambda because it's a nameless function
_ : (𝓁 : Level) → Type (lsuc 𝓁)
_ = λ 𝓁 → Type 𝓁

-- these are implicitly generalized variables
variable
  ℓ : Level