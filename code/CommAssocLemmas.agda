open import Level
open import Data.Product
open import Relation.Binary using (Setoid; _Preserves₂_⟶_⟶_)
open import Algebra.Structures
module CommAssocLemmas (A : Set) (_≈_ : A -> A -> Set) (_+_ : A -> A -> A) (zer : A) 
         (isCommMon : IsCommutativeMonoid _≈_ _+_ zer) where

  SA : Setoid _ _
  SA = record {Carrier = A; _≈_ = _≈_; isEquivalence = IsCommutativeMonoid.isEquivalence isCommMon}

  --  open Relation.Binary.Setoid SA
  open import Algebra.FunctionProperties public
  open IsCommutativeMonoid isCommMon public renaming (∙-cong to _<+>_)
 
  open import Relation.Binary.EqReasoning SA
  lemmaCommAssoc00 : ∀ a b c d ->  (a + ((b + c) + (d + zer))) ≈ ((a + c) + (b + d))
  lemmaCommAssoc00 a b c d = 
    begin
      (a     + ((b + c)    + (d + zer)))
    ≈⟨ refl <+> (refl     <+> proj₂ identity d) ⟩
      (a     + ((b + c)    + d))
    ≈⟨ refl <+> (comm b c <+> refl) ⟩
      (a     + ((c + b)    + d))
    ≈⟨ refl <+> assoc c b d ⟩
      (a     + (c + (b + d)))
    ≈⟨ sym (assoc a c (b + d)) ⟩
      ((a + c) + (b + d))
    ∎

--  lemmaCommAssoc00 : ∀ a b c d ->  (a + ((b + c) + d)) ≈ ((a + c) + (b + d))

  lemmaCommAssoc01 : ∀ {a} {b} {c} {d} {e} -> (a + ((b + c)  + (d + e))) ≈ (((a + c) + d) + (b + e))
  lemmaCommAssoc01 {a} {b} {c} {d} {e} = 
    begin
      (a     +  ((b + c)  + (d + e)))
    ≈⟨ refl <+> assoc b c (d + e) ⟩
      (a     +  (b     + (c + (d + e))))
    ≈⟨ refl <+> (refl <+> sym (assoc c d e)) ⟩
      (a     +  (b     + ((c + d) + e)))
    ≈⟨ refl <+> (sym (assoc b (c + d) e)) ⟩
      (a     +  ((b + (c + d))   +  e))
    ≈⟨ refl <+> (comm b (c + d) <+> refl) ⟩
      (a     +  (((c + d) + b) + e))
    ≈⟨ refl <+> (assoc (c + d) b e) ⟩
      (a     +  ((c + d) + (b + e)))
    ≈⟨ sym (assoc a (c + d) (b + e))⟩
      ((a + (c + d)) + (b + e))
    ≈⟨ sym (assoc a c d) <+> refl ⟩
      (((a + c) + d) + (b + e))
    ∎

{-
  lemmaCommAssoc11 : ∀ a b c d ->  (a + (b + (c + d))) ≈ ((a + c) + (b + d))
  lemmaCommAssoc11 a b c d = 
    begin
      (a     + (b + (c    + d)))
    ≈⟨ refl <+> (sym (assoc b c d)) ⟩
      (a     + ((b + c)    + d))
    ≈⟨ lemmaCommAssoc00 a b c d ⟩
      ((a + c) + (b + d))
    ∎
-}

--  open Lemmas public 
  
