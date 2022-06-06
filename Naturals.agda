{-# OPTIONS --without-K --exact-split --safe #-}

module Naturals where

open import Universes public

data ℕ : Type₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- we can do induction over every element of ℕ
-- when A n is a subsingleton type (e.g. a proof of equality), then this is regular proof by induction
-- if it's not, and it's actually a computation, this gives us a way to calculate A n?
ℕ-induction : (A : ℕ → Type ℓ) -- given some property that we want to prove holds for every N
  → A 0 -- and the base case
  → ( (n : ℕ) → A n → A (succ n) ) -- and a way to prove that An+1 from An
  → (n : ℕ) -- then for any Nat
  → A n -- we can show that A n is true
ℕ-induction A base-case inductive-step zero = base-case
ℕ-induction A base-case inductive-step (succ x) = inductive-step x (ℕ-induction A base-case inductive-step x)

-- this is non-dependent ℕ-induction (p50). It is ℕ-induction with a constant A family
ℕ-recursion : (X : Type ℓ) -- given something we want to prove
  → X -- and a proof that it holds
  → (ℕ → X → X) -- and a way to prove it for succ(n)
  → ℕ -- then for any Nat
  → X -- then we can ???
ℕ-recursion X x iterate-f n = ℕ-induction (λ _ → X) x iterate-f n

ℕ-iteration : (X : Type ℓ) -- given some property
  → X -- and a proof that it holds
  → (X → X) -- and a way to prove the successor
  → ℕ -- then for any Nat
  → X -- we can prove it holds N steps down
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)
