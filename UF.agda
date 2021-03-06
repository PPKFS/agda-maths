{-# OPTIONS --without-K --exact-split --safe #-}

module UF where

open import Universes public


data π : Typeβ where
  β : π

-- if we have a property of π, and we have a proof (an element of the type) that A holds for β, then for any x
-- we have a proof that A holds for x.
π-induction : (A : π β Type β) β A β β (x : π) β A x
π-induction A a β = a

-- given some type, and an element of that type, we can make a function that maps any element of π to it
π-recursion : (B : Type β) β B β (π β B)
π-recursion _ b = Ξ» _ β b

-- but we can also write this with π-induction; the *type* B is some property we wish to show holds, and we have a general proof of this
-- , then for any x in π we have a proof that A holds.
π-recursionβ : (B : Type β) β B β π β B
π-recursionβ B b x = π-induction (Ξ» _ β B) b x

-- for any type X, we have a unique function X β π
!πβ : (X : Type β) β X β π
!πβ _ _ = β

-- for any type X, we have a unique function X β π but we don't need to have the type manually
!π : {X : Type β} (x : X) β π
!π _ = β

-- the empty type
data π : Typeβ where

-- given a property of the empty type (per element), and a member of the empty type (we can't do that), 
-- we can show that the property holds for every element by accepting our premise was absurd by the ()
π-induction : (A : π β Type β) β (x : π) β A x
π-induction A ()

-- recursion here is that given some type, we can construct the function that maps the empty type to it by giving up immediately
π-recursion : (A : Type β) β π β A
π-recursion A ()

-- or if we use induction, then we are saying that for every element x of the empty type, we wish to show that A x exists, and our example of
-- this is by taking our element a of the empty type (which is absurd) and then introducing A a (which is absurd) but it holds just fine
π-recursionβ : (A : Type β) β π β A
π-recursionβ A a = π-induction (Ξ» _ β A) a

-- the unique function from empty to a type is absurd
!π : (A : Type β) β π β A
!π = π-recursion

-- we can say a type is empty (so considering it a property is just...false) if there is a way to map it to the empty type
-- because the only way this holds is if there is no element in the type; π β π is the 'only' way to satisfy this
is-empty : Type β β Type β
is-empty X = X β π