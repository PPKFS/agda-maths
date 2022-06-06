module NaturalOrder where

open import Naturals public
open import Universes public
open import UF public

_≤_ _≥_ : ℕ → ℕ → Type₀

0 ≤ x = 𝟙
succ x ≤ 0 = 𝟘
x ≤ succ y = {!   !}

x ≥ y = y ≤ x

infix 10 _≤_
infix 10 _≥_