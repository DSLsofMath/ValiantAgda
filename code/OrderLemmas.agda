import Relation.Binary.Reasoning.Setoid as EqReasoning
open import SemiNearRingRecords
module OrderLemmas (snro : SemiNearRing) where

open SemiNearRing snro -- public
open import CommAssocLemmas s _≃s_ _+s_ zers isCommMon
     using (assoc; comm)
     renaming (SA to Ss)

open EqReasoning Ss

monoPlusLeft : ∀ {a} {b} {c} →  a ≤s b  →
                        (a +s c)  ≤s  (b +s c)
monoPlusLeft {a} {b} {c} a≤b =
  begin
    (a +s c)  +s  (b +s c)
  ≈⟨ assoc _ _ _ ⟩
    a +s (c  +s  (b +s c))
  ≈⟨ refls <+> comm _ _ ⟩
    a +s ((b +s c) +s c)
  ≈⟨ refls <+> assoc _ _ _ ⟩
    a +s (b +s (c +s c))
  ≈⟨ sym (assoc _ _ _) ⟩
    (a +s b) +s (c +s c)
  ≈⟨ a≤b <+> idem _ ⟩
    b +s c
  ∎

monoTimesLeft : ∀ {a} {b} {c} →  a ≤s b →
                         (a *s c)  ≤s  (b *s c)
monoTimesLeft {a} {b} {c} a≤b =
  begin
    (a *s c) +s (b *s c)
  ≈⟨ sym (distr _ _ _) ⟩
    (a +s b) *s c
  ≈⟨  a≤b    <*> refls  ⟩ -- a≤=b means a+b==b
          b  *s c
  ∎
infixl 6 _[+]_
infixl 7 _[*]_

_[+]_ : ∀ {a} {a'} {b} {b'} ->  a ≤s a' -> b ≤s b' ->
                                (a +s b) ≤s (a' +s b')
_[+]_ {a} {a'} {b} {b'} pa pb =
  begin
    (a +s b) +s (a' +s b')
  ≈⟨ assoc _ _ _ ⟩
    a +s (b +s (a' +s b'))
  ≈⟨  refls <+> comm _ _  ⟩
    a +s ((a' +s b') +s b)
  ≈⟨  refls <+> assoc _ _ _  ⟩
    a +s (a' +s (b' +s b))
  ≈⟨  sym (assoc _ _ _)  ⟩
    (a +s a') +s (b' +s b)
  ≈⟨  pa <+> comm _ _  ⟩
    a' +s (b +s b')
  ≈⟨  refls <+> pb  ⟩
    a' +s b'
  ∎

_[*]_ : ∀ {a} {a'} {b} {b'} ->  a ≤s a' -> b ≤s b' ->
                                (a *s b) ≤s (a' *s b')
_[*]_ {a} {a'} {b} {b'} pa pb =
  begin
    (a *s b) +s (a' *s b')
  ≈⟨  refls <+> (sym pa <*> refls)  ⟩
    a *s b +s (a +s a') *s b'
  ≈⟨  refls <+> distr _ _ _  ⟩
    a *s b +s (a *s b' +s a' *s b')
  ≈⟨  sym (assoc _ _ _)  ⟩
    (a *s b +s a *s b') +s a' *s b'
  ≈⟨  sym (distl _ _ _) <+> (refls <*> sym pb)  ⟩
    a *s (b +s b') +s a' *s (b +s b')
  ≈⟨  sym (distr _ _ _)  ⟩
    (a +s a') *s (b +s b')
  ≈⟨  pa <*> pb  ⟩
    a' *s b'
  ∎


≤s-trans : ∀ {a b c} →  a ≤s b  →  b ≤s c  →  a ≤s c
≤s-trans {a} {b} {c} p q =
  begin
    a +s c
  ≈⟨  refls <+> sym q ⟩
    a +s (b +s c)
  ≈⟨  sym (assoc _ _ _) ⟩
    (a +s b) +s c
  ≈⟨  p <+> refls ⟩
    b +s c
  ≈⟨ q ⟩
    c
  ∎

≃sTo≤s : ∀ {a b} →  a ≃s b  →  a ≤s b
≃sTo≤s {a} {b} a=b =
  begin
    a +s b
  ≈⟨ a=b <+> refls ⟩
    b +s b
  ≈⟨ idem _ ⟩
    b
  ∎
