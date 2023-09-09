import Relation.Binary.Reasoning.Setoid as EqReasoning
open import SemiNearRingRecords
module ZeroLemmas (snr : SemiNearRing) where
  open SemiNearRing snr -- public
  open import CommAssocLemmas s _≃s_ _+s_ zers isCommMon hiding (_<+>_) renaming (SA to Ss)

  zeroˡLemma : ∀ x y → zers *s x +s zers *s y ≃s zers
  zeroˡLemma x y = begin
         zers *s x +s zers *s y
       ≈⟨ zeroˡ x <+> zeroˡ y ⟩
         zers +s zers
       ≈⟨ identityˡs zers ⟩
         zers
       ∎
    where open EqReasoning Ss

  zeroʳLemma : ∀ x y →  x *s zers  +s  y *s zers   ≃s  zers
  zeroʳLemma x y =
       begin
           x *s zers  +s   y *s zers
       ≈⟨  zeroʳ x    <+>  zeroʳ y ⟩
         zers         +s   zers
       ≈⟨ identityˡs zers ⟩
         zers
       ∎
    where open EqReasoning Ss

  zeroˡʳLemma : ∀ w x y → w +s (zers *s x +s  y *s zers)  ≃s  w
  zeroˡʳLemma w x y = begin
        w +s (zers *s x  +s  y *s zers)
     ≈⟨ refls <+> (zeroˡ x <+> zeroʳ y) ⟩
        w +s (zers +s zers)
     ≈⟨ refls <+> identityˡs zers ⟩
        w +s zers
     ≈⟨ identityʳs w ⟩
        w
     ∎
     where open EqReasoning Ss


  -- Some lemmas are needed to eliminate the zers and massage the terms.
  zeroLemma01 = lemmaCommAssoc01

  zeroLemma10 : ∀ {a b c d e} →   a +s ( ((zers *s b) +s c) +s (d +s (e *s zers)))
                              ≃s  a +s                 ( c  +s  d )
  zeroLemma10 {a} {b} {c} {d} {e} = refls <+>
    (begin
       ((zers *s b) +s c)      +s (d      +s (e *s zers))
     ≈⟨ (zeroˡ   b <+> refls) <+> (refls <+>  zeroʳ e) ⟩
       ( zers       +s c)      +s (d      +s zers)
     ≈⟨ identityˡs c <+> identityʳs d ⟩
        c +s d
     ∎)
      where open EqReasoning Ss

  zeroLemma00 : ∀ {a b c d e} →   a +s ((c +s b) +s (d +s (e *s zers)) )
                             ≃s  (a +s b) +s (c  +s  d)
  zeroLemma00 {a} {b} {c} {d} {e} =
    (begin
       a       +s ((c +s b)   +s (d      +s (e *s zers)) )
     ≈⟨ refls <+> (comms c b <+> (refls <+> zeroʳ e)) ⟩
       a       +s ((b +s c)   +s (d      +s zers) )
     ≈⟨ refls <+> (refls <+> identityʳs d) ⟩
       a       +s ((b +s c)   +s d)
     ≈⟨ refls <+> assocs b c d ⟩
       a +s (b +s (c +s d))
     ≈⟨ syms (assocs a b _) ⟩
       (a +s b) +s (c +s d)
     ∎)
      where open EqReasoning Ss

  zeroLemma11 : ∀ {a b c d e} →   a +s (((zers *s e)  +s  c) +s (b +s d))
                             ≃s  (a +s b) +s (c +s  d)
  zeroLemma11 {a} {b} {c} {d} {e} =
    (begin
       a       +s (((zers *s e)  +s  c)     +s (b +s d))
     ≈⟨ refls <+> ((zeroˡ e     <+> refls) <+> refls) ⟩
       a       +s ((zers        +s  c)      +s (b +s d))
     ≈⟨ refls <+> (identityˡs c            <+> refls) ⟩
       a       +s (                 c       +s (b +s d))
     ≈⟨ refls <+> syms (assocs c b d) ⟩
       a       +s ((c +s b) +s d)
     ≈⟨ refls <+> (comms c b <+> refls) ⟩
       a       +s ((b +s c) +s d)
     ≈⟨ refls <+> (assocs _ _ _) ⟩
       a       +s (b +s (c +s d))
     ≈⟨ syms (assocs _ _ _) ⟩
       (a +s b) +s (c +s d)
     ∎)
      where open EqReasoning Ss
