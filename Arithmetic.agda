module Arithmetic where

open import Naturals public

_+_  _×_ : ℕ → ℕ → ℕ

-- x + 0 = x
-- x + succ y = succ (x + y)

x + y = ℕ-iteration ℕ x succ y

x × y = ℕ-iteration ℕ 0 (x +_) y
-- x × 0 = 0
-- x × succ y = x + (x × y)

infixl 20 _+_
infixl 21 _×_