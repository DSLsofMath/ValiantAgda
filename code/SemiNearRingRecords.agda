import Algebra.Definitions using (LeftZero; RightZero; _DistributesOverˡ_;_DistributesOverʳ_; Idempotent)
import Function using (_on_)
import Level
import Relation.Binary.Reasoning.Setoid as EqReasoning
import Relation.Binary.Construct.On using (isEquivalence)
import Algebra.Structures using (module IsCommutativeMonoid; IsCommutativeMonoid)
open import Relation.Binary    using (module IsEquivalence; IsEquivalence; _Preserves₂_⟶_⟶_ ; Setoid)
open import Data.Product renaming (_,_ to _,,_) -- just to avoid clash with other commas
                         hiding (_<*>_)
open import Preliminaries using (Rel; UniqueSolution; LowerBound)

module SemiNearRingRecords where

record SemiNearRing : Set₁ where                  -- \structure{1}{|SemiNearRing|}
  field                                           -- \structure{1.1}{Carriers, operators}
     s : Set
     _≃s_  : s → s → Set
     zers  : s
     _+s_  : s → s → s
     _*s_  : s → s → s

  open Algebra.Structures         using (IsCommutativeMonoid)
  open Algebra.Definitions _≃s_   using (LeftZero; RightZero)

  field                                           -- \structure{1.2}{Commutative monoid |(+,0)|}
    isCommMon : IsCommutativeMonoid _≃s_ _+s_ zers

    zeroˡ  : LeftZero   zers  _*s_   -- expands to |∀ x →  (zers *s x)  ≃s  zers|
    zeroʳ  : RightZero  zers  _*s_   -- expands to |∀ x →  (x *s zers)  ≃s  zers|
    _<*>_  : ∀ {x y u v} →  (x ≃s y)  →  (u ≃s v)  →  (x *s u   ≃s   y *s v)

  open Algebra.Definitions _≃s_
    using (Idempotent; _DistributesOverˡ_; _DistributesOverʳ_)

  field                                           -- \structure{1.3}{Distributive, idempotent, \ldots}
     idem   : Idempotent _+s_

     distl  : _*s_ DistributesOverˡ _+s_
     distr  : _*s_ DistributesOverʳ _+s_
       -- expands to |∀ a b c →  (a +s b) *s c   ≃s   (a *s c) +s (b *s c)|

  infix  4 _≤s_
  _≤s_ : s -> s -> Set
  x ≤s y =  x +s y ≃s y

  infix 4 _≃s_; infixl 6 _+s_; infixl 7 _*s_

                                                  -- \structure{1.4}{Exporting commutative monoid operations}
  open Algebra.Structures.IsCommutativeMonoid isCommMon public
    hiding (refl)
    renaming
     (  isEquivalence  to isEquivs
     ;  assoc          to assocs
     ;  comm           to comms
     ;  ∙-cong         to _<+>_
     ;  identityˡ      to identityˡs
     )
  identityʳs = proj₂ identity

  sSetoid : Setoid Level.zero Level.zero          -- \structure{1.5}{Setoid, \ldots}
  sSetoid = record {  Carrier        = s;
                      _≈_            = _≃s_;
                      isEquivalence  = isEquivs }

  open IsEquivalence isEquivs public
    hiding   (reflexive; isPartialEquivalence) renaming (refl to refls ; sym to syms ; trans to transs)

  LowerBounds  = LowerBound  _≤s_                 -- \structure{1.6}{Lower bounds}

record SemiNearRing2 : Set₁ where                 -- \structure{2}{|SemiNearRing2|}
  field
    snr : SemiNearRing
  open SemiNearRing snr public   -- public = export the "local" names from |SemiNearRing|
  field                                           -- \structure{2.1}{Plus and times for |u|, \ldots}
     u : Set
     _+u_  : u → u → u
     _*u_  : u → u → u
     u2s   : u → s

  _≃u_ : u → u → Set
  _≃u_  = _≃s_ Function.on u2s

  _u*s_ : u → s → s
  _u*s_ u s =   u2s u  *s  s

  _s*u_ : s → u → s
  _s*u_ s u =   s  *s  u2s u

  infix   4  _≃u_;  infixl  6  _+u_;  infixl  7  _*u_ _u*s_ _s*u_

  uSetoid : Setoid Level.zero Level.zero
  uSetoid = record { isEquivalence = Relation.Binary.Construct.On.isEquivalence u2s isEquivs }

  _≤u_  : u → u → Set
  _≤u_  = _≤s_ Function.on u2s

  L : u → s → u → s → Set                         -- \structure{2.2}{Linear equation |L|}
  L a y b x =  y  +s  (a u*s x  +s  x s*u b) ≃s x

                                                  -- \structure{2.3}{Properties of |L|}
  UniqueL  = ∀ {a y b} → UniqueSolution _≃s_ (L a y b)
  CongL    = ∀ {a x b} -> ∀ {y y'} -> y ≃s y' -> L a y b x -> L a y' b x
