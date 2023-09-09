open import Data.Product renaming (_,_ to _,,_) -- just to avoid clash with other commas
open import Algebra.Structures    using (IsSemigroup)
open import Algebra.Definitions   using (LeftIdentity; Commutative)

module Preliminaries where

Rel : Set -> Set₁
Rel A  =  A -> A -> Set

Entire : {A B : Set} -> (_R_ : A -> B -> Set) -> Set
Entire _R_ = ∀ a -> ∃ \ b -> a R b

fun : {A B : Set} -> {_R_ : A -> B -> Set} -> Entire _R_ -> A -> B
fun ent a = proj₁ (ent a)

correct :  {A B : Set} -> {_R_ : A -> B -> Set} -> (ent : Entire _R_) ->
           let f = fun ent in  ∀ {a : A} -> a R (f a)
correct ent {a} = proj₂ (ent a)

Entire3 : {A B C D : Set} -> (R : A -> B -> C -> D -> Set) -> Set
Entire3 R = ∀ x y z -> ∃ (R x y z)

fun3 : {A B C D : Set} -> {R : A -> B -> C -> D -> Set} -> Entire3 R -> A -> B -> C -> D
fun3 ent a b c = proj₁ (ent a b c)

correct3 :  {A B C D : Set} -> {R : A -> B -> C -> D -> Set} -> (e : Entire3 R) ->
           ∀ {a : A} {b : B} {c : C} -> R a b c (fun3 e a b c)
correct3 ent {a} {b} {c} = proj₂ (ent a b c)

UniqueSolution : {A : Set} -> Rel A -> (A -> Set) -> Set
UniqueSolution _≃_ P = ∀ {x y} -> P x -> P y  ->  x ≃ y

LowerBound : {A : Set} -> Rel A -> (A -> Set) -> (A -> Set)
LowerBound _≤_ P  a = ∀ z -> (P z -> a ≤ z)

Least   : {A : Set} -> Rel A -> (A -> Set) -> (A -> Set)
Least   _≤_ P  a =  P a  ×  LowerBound _≤_ P a
