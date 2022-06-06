{-# OPTIONS --without-K --exact-split --safe #-}

module UF where

open import Universes public


data 𝟙 : Type₀ where
  ⋆ : 𝟙

-- if we have a property of 𝟙, and we have a proof (an element of the type) that A holds for ⋆, then for any x
-- we have a proof that A holds for x.
𝟙-induction : (A : 𝟙 → Type ℓ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

-- given some type, and an element of that type, we can make a function that maps any element of 𝟙 to it
𝟙-recursion : (B : Type ℓ) → B → (𝟙 → B)
𝟙-recursion _ b = λ _ → b

-- but we can also write this with 𝟙-induction; the *type* B is some property we wish to show holds, and we have a general proof of this
-- , then for any x in 𝟙 we have a proof that A holds.
𝟙-recursion₁ : (B : Type ℓ) → B → 𝟙 → B
𝟙-recursion₁ B b x = 𝟙-induction (λ _ → B) b x

-- for any type X, we have a unique function X → 𝟙
!𝟙₁ : (X : Type ℓ) → X → 𝟙
!𝟙₁ _ _ = ⋆

-- for any type X, we have a unique function X → 𝟙 but we don't need to have the type manually
!𝟙 : {X : Type ℓ} (x : X) → 𝟙
!𝟙 _ = ⋆

-- the empty type
data 𝟘 : Type₀ where

-- given a property of the empty type (per element), and a member of the empty type (we can't do that), 
-- we can show that the property holds for every element by accepting our premise was absurd by the ()
𝟘-induction : (A : 𝟘 → Type ℓ) → (x : 𝟘) → A x
𝟘-induction A ()

-- recursion here is that given some type, we can construct the function that maps the empty type to it by giving up immediately
𝟘-recursion : (A : Type ℓ) → 𝟘 → A
𝟘-recursion A ()

-- or if we use induction, then we are saying that for every element x of the empty type, we wish to show that A x exists, and our example of
-- this is by taking our element a of the empty type (which is absurd) and then introducing A a (which is absurd) but it holds just fine
𝟘-recursion₁ : (A : Type ℓ) → 𝟘 → A
𝟘-recursion₁ A a = 𝟘-induction (λ _ → A) a

-- the unique function from empty to a type is absurd
!𝟘 : (A : Type ℓ) → 𝟘 → A
!𝟘 = 𝟘-recursion

-- we can say a type is empty (so considering it a property is just...false) if there is a way to map it to the empty type
-- because the only way this holds is if there is no element in the type; 𝟘 → 𝟘 is the 'only' way to satisfy this
is-empty : Type ℓ → Type ℓ
is-empty X = X → 𝟘