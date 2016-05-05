open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.EqReasoning as EqReasoning
open import Algebra.FunctionProperties using (LeftZero; RightZero)
open import Algebra.Structures using (module IsCommutativeMonoid;
                                             IsCommutativeMonoid)
open import Data.Product
  -- just to avoid clash with other commas
open import Data.Unit
import OrderLemmas
import Level
open import SemiNearRingRecords
open import Preliminaries

module ValiantRefinement where

record ClosedSemiNearRing : Set₁ where            -- \structure{3}{|ClosedSemiNearRing|}

  field
    snr2 : SemiNearRing2  -- includes |s|, |u| and corresponding operations

  open SemiNearRing2 snr2

  Q : u → u → Set                                 -- \structure{3.1}{Quadratic equation |Q| + properties}
  Q w c = w  +u  c *u c  ≃u  c

  Closure : u -> u -> Set
  Closure w c = Least _≤u_ (Q w) c

  field
    entireQ : Entire Q
  closure : u → u                                 -- \structure{3.2}{Closure function and correctness}
  closure = fun entireQ

  closureHasAll  : ∀ {w : u} → Q w (closure w)
  closureHasAll  = correct entireQ
  field                                           -- \structure{3.3}{Function for |L| and its correctness}
    entireL    : Entire3 L

  completion : u → s → u → s
  completion = fun3 entireL

  completionHasAll : ∀ {a y b} →  L a y b (completion a y b)
  completionHasAll = correct3 entireL

  field                                           -- \structure{3.4}{Ordering properties of |L| and |Q|}
    uniqueL         : UniqueL
    congL           : CongL
    completionMono  : ∀ {a a' y y' b b'} →   a ≤u a'  →  y ≤s y'  →  b ≤u b'  →
                                             completion a y b ≤s completion a' y' b'
    closureIsLeast  : {w : u} -> LowerBound _≤u_ (Q w) (closure w)

  open OrderLemmas snr public

  completionIsLeast : ∀ (a : u) (y : s) (b : u) -> LowerBounds (L a y b) (completion a y b)
  completionIsLeast a y b z p = ≃sTo≤s (uniqueL completionHasAll p)

  open SemiNearRing2 snr2 public
                                                  -- \structure{4}{2-by-2 block matrix, preserving |ClosedSemiNearRing|}
Square : ClosedSemiNearRing -> ClosedSemiNearRing
Square csnr = CSNR where
  open ClosedSemiNearRing csnr

  record S : Set where                            -- \structure{4.1}{Square matrix}
    constructor ⟨_,_,_,_⟩
    field
      s00  : s;  s01  : s
      s10  : s;  s11  : s
  infix 4 ⟨_,_,_,_⟩

  record U : Set where                            -- \structure{4.2}{Upper triangular matrix}
    constructor ⟨_,_,•,_⟩
    field
      uu00 : u;  us01  : s;
                 uu11  : u
  infix 4 ⟨_,_,•,_⟩

  _+S_  : S →  S → S
  _+S_  ⟨ a         ,  b         ,  c         ,  d         ⟩
        ⟨       a'  ,        b'  ,        c'  ,        d'  ⟩ =
        ⟨ a +s  a'  ,  b +s  b'  ,  c +s  c'  ,  d +s  d'  ⟩

  _*S_  : S → S → S
  _*S_  ⟨  a  , b ,
           c  , d ⟩  ⟨  a'  , b'  ,
                        c'  , d'  ⟩  =  ⟨  (a *s a')  +s  (b *s c')  ,  (a *s b')  +s  (b *s d')
                                        ,  (c *s a')  +s  (d *s c')  ,  (c *s b')  +s  (d *s d') ⟩

  infixl  6  _+S_
  infixl  7  _*S_

  zerS : S
  zerS = ⟨  zers , zers ,
            zers , zers ⟩

  _+U_  : U → U → U
  _+U_ ⟨ xl , xm ,•, xr ⟩ ⟨ yl , ym ,•, yr ⟩ = ⟨ xl +u yl , xm +s ym ,•, xr +u yr ⟩

  _*U_ : U → U → U
  _*U_  ⟨  xl  ,  xm
           ,•,    xr ⟩  ⟨  yl ,   ym
                           ,•,    yr ⟩  =  ⟨  xl *u yl  ,   xl u*s ym  +s  xm s*u yr
                                              ,•,           xr *u yr                  ⟩

  _≃S_ : S → S → Set
  _≃S_ ⟨ a , b , c , d ⟩ ⟨ a' , b' , c' , d' ⟩  =  (a ≃s a')  ×  (b ≃s b')
                                                ×  (c ≃s c')  ×  (d ≃s d')

  infix 4 _≃S_

  U2S : U → S
  U2S ⟨ uu00 , us01 ,•, uu11 ⟩ =  ⟨  u2s uu00  ,  us01      ,
                                     zers      ,  u2s uu11   ⟩

  reflS : {x : S} → x ≃S x                        -- \structure{4.3}{Laws}
  reflS =  refls , refls ,
           refls , refls

  symS : {i j : S} → i ≃S j → j ≃S i
  symS (p00 , p01 , p10 , p11) = ( syms p00 , syms p01 , syms p10 , syms p11 )

  transS : {i j k : S} →  i ≃S j  →  j ≃S k  →  i ≃S k
  transS  (p00 , p01 , p10 , p11) (q00 , q01 , q10 , q11) =
          ( transs p00 q00 , transs p01 q01 , transs p10 q10 , transs p11 q11 )

  assocS : (x y z : S) →  (x +S y) +S z  ≃S  x +S (y +S z)
  assocS  ⟨ x00  , x01  , x10  , x11 ⟩
          ⟨ y00  , y01  , y10  , y11 ⟩
          ⟨ z00  , z01  , z10  , z11 ⟩ =
          (  assocs x00  y00  z00  , assocs x01  y01  z01 ,
             assocs x10  y10  z10  , assocs x11  y11  z11 )

  _<+S>_ : {a1 a2 b1 b2 : S} →  a1 ≃S a2  →  b1 ≃S b2  →  a1 +S b1  ≃S  a2 +S b2
  _<+S>_  (p00 , p01 , p10 , p11) (q00 , q01 , q10 , q11) =
          (  (p00  <+> q00)  , (p01  <+> q01)  ,
             (p10  <+> q10)  , (p11  <+> q11)  )

  _<*S>_ : {x1 y1 x2 y2 : S} →  x1 ≃S x2  →  y1 ≃S y2  →  x1 *S y1  ≃S  x2 *S y2
  _<*S>_ (p00 , p01 , p10 , p11) (q00 , q01 , q10 , q11) =
         (  (p00  <*> q00) <+> (p01  <*> q10) , (p00  <*> q01) <+> (p01  <*> q11)  ,
            (p10  <*> q00) <+> (p11  <*> q10) , (p10  <*> q01) <+> (p11  <*> q11)  )

  swapMid : ∀ {a b c d}  →   (a +s b)  +s  (c +s d)
                         ≃s  (a +s c)  +s  (b +s d)

  swapMid {a} {b} {c} {d}
           =  begin
                (a +s b) +s (c +s d)
              ≈⟨ assocs _ _ _ ⟩
                 a +s (b +s (c +s d))
              ≈⟨ refls <+> sym (assocs _ _ _) ⟩
                 a +s ((b +s c) +s d)
              ≈⟨ refls <+> (comms _ _ <+> refls) ⟩
                a +s ((c +s b) +s d)
              ≈⟨ refls <+> (assocs _ _ _) ⟩
                a +s (c +s (b +s d))
              ≈⟨ sym (assocs _ _ _) ⟩
                (a +s c) +s (b +s d)
              ∎
     where open EqReasoning sSetoid


  distlS : (x y z : S) → x *S (y +S z) ≃S x *S y +S x *S z
  distlS _ _ _ =  distrHelp , distrHelp , distrHelp , distrHelp
     where  distrHelp : ∀ {a b c d e f}  →   a *s (b +s c)       +s  d *s (e +s f)
                                         ≃s  (a *s b +s d *s e)  +s (a *s c +s d *s f)
            distrHelp = transs (distl _ _ _ <+> distl _ _ _) swapMid


  distrS : (x y z : S) → (y +S z) *S x ≃S y *S x +S z *S x
  distrS _ _ _ = distrHelp , distrHelp , distrHelp , distrHelp
     where  distrHelp : ∀ {a b c d e f}  →  (a +s b) *s c       +s (d +s e) *s f
                                         ≃s (a *s c +s d *s f)  +s (b *s c +s e *s f)
            distrHelp = transs (distr _ _ _ <+> distr _ _ _) swapMid

  identityˡS : (x : S) →  zerS +S x  ≃S  x
  identityˡS ⟨ s00 , s01 , s10 , s11 ⟩ =  identityˡs s00 , identityˡs s01 , identityˡs s10 , identityˡs s11

  commS : (x y : S) →  x +S y ≃S y +S x
  commS  ⟨ x00 , x01 , x10 , x11 ⟩ ⟨ y00 , y01 , y10 , y11 ⟩ =  (comms x00 y00 , comms x01 y01 ,
                                                                 comms x10 y10 , comms x11 y11 )

  idemS : (x : S) → x +S x  ≃S  x
  idemS ⟨ x00 , x01 , x10 , x11 ⟩ = ( idem x00 , idem x01 , idem x10 , idem x11 )

  open import ZeroLemmas snr

  zeroˡS : LeftZero _≃S_ zerS _*S_
  zeroˡS ⟨ s00 , s01 , s10 , s11 ⟩ = ( zeroˡLemma s00 s10 , zeroˡLemma s01 s11 , zeroˡLemma s00 s10 , zeroˡLemma s01 s11)

  zeroʳS : RightZero _≃S_ zerS _*S_
  zeroʳS ⟨ s00 , s01 , s10 , s11 ⟩ = ( zeroʳLemma s00 s01 , zeroʳLemma s00 s01 , zeroʳLemma s10 s11 , zeroʳLemma s10 s11)

  isCommMonS : IsCommutativeMonoid _≃S_ _+S_ zerS
  isCommMonS = record {
     isSemigroup = record {
        isEquivalence  = record { refl = reflS; sym = symS; trans = transS };
        assoc          = assocS;
        ∙-cong         = _<+S>_ };
     identityˡ   = identityˡS;
     comm        = commS }

  SNR : SemiNearRingRecords.SemiNearRing
  SNR = record {
           s         = S;
           zers      = zerS;
           _+s_      = _+S_;
           _≃s_      = _≃S_;
           isCommMon = isCommMonS;
           _*s_      = _*S_;
           zeroˡ     = zeroˡS;
           zeroʳ     = zeroʳS;
           _<*>_     = _<*S>_;
           distr     = distrS;
           distl     = distlS;
           idem      = idemS
           }

  SNR2 : SemiNearRing2
  SNR2 = record {
           snr       = SNR ;
           u         = U;
           _+u_      = _+U_;
           _*u_      = _*U_;
           u2s       = U2S }

  _≃U_ : U → U → Set
  _≃U_ = SemiNearRing2._≃u_ SNR2

  _U*S_ : U → S → S
  _U*S_ = SemiNearRing2._u*s_ SNR2

  _S*U_ : S → U → S
  _S*U_ = SemiNearRing2._s*u_ SNR2

  congU :  ∀ {x1 x2 y1 y2 z1 z2} → x1 ≃u x2  →  y1 ≃s y2  →  z1 ≃u z2  →
           ⟨ x1 , y1 ,•, z1 ⟩ ≃U ⟨ x2 , y2 ,•, z2 ⟩
  congU p1 p2 p3 = (p1 , p2 , refls , p3)

  congS :  ∀ {x1 x2 y1 y2 z1 z2 w1 w2} →
           x1 ≃s x2  →  y1 ≃s y2  →  z1 ≃s z2  →  w1 ≃s w2  →
           ⟨ x1 , y1 , z1 , w1 ⟩ ≃S ⟨ x2 , y2 , z2 , w2 ⟩
  congS p1 p2 p3 p4 = (p1 , p2 , p3 , p4)

  QU = \ W C -> (W  +U  (C *U C)) ≃U C            -- \structure{4.4}{Lifting |Q| and its proof}

  entireQStep : ∀ W -> ∃ (QU W)
  entireQStep W = C , proof where
         C : U
         C = _

         open EqReasoning (SemiNearRing2.uSetoid SNR2)
         proof : (W  +U  (C *U C))  ≃U  C
         proof =  begin
                    (W  +U  (C *U C))
                  ≡⟨ refl ⟩  -- expand matrix components
                    let   ⟨ A   , Y   ,•, B    ⟩ = W
                          ⟨ A'  , Y'  ,•, B'   ⟩ = C in
                    ⟨ A , Y ,•, B ⟩  +U (⟨ A' , Y' ,•, B' ⟩ *U ⟨ A' , Y' ,•, B' ⟩)
                  ≡⟨ refl ⟩  -- expand definition of |*U|
                    ⟨ A , Y ,•, B ⟩  +U   ⟨ A' *u A'  ,  (A' u*s Y'  +s Y' s*u B')
                                                      ,•,  B' *u B' ⟩
                  ≡⟨ refl ⟩  -- by def. of |+U|
                    ⟨  A +u A' *u A'      ,     Y +s (A' u*s Y'  +s  Y' s*u B')
                                          ,•,   B +u B' *u B'  ⟩
                  ≈⟨ congU closureHasAll completionHasAll closureHasAll ⟩
                    ⟨ A' , Y' ,•, B' ⟩
                  ≡⟨ refl ⟩
                     C
                  ∎

  entireQStep2 : ∀ W -> ∃ (QU W)
  entireQStep2 W = C , proof where
         C : U

         C =  let   ⟨ A , Y ,•, B ⟩  = W
                    (A' , proofA)    = entireQ A
                    (B' , proofB)    = entireQ B
                    (Y' , proofY)    = entireL A' Y B'
              in    ⟨ A' , Y' ,•, B' ⟩

         open EqReasoning (SemiNearRing2.uSetoid SNR2)
         proof : (W  +U  (C *U C))  ≃U  C

         proof = congU closureHasAll completionHasAll closureHasAll

  _≤U_ = SemiNearRing2._≤u_  SNR2                 -- \structure{4.5}{Lifting orders and their properties}
  _≤S_ = SemiNearRing2._≤s_  SNR2
  closureIsLeastS : ∀ {W} -> LowerBound _≤U_ (QU W) (fun entireQStep W)
  closureIsLeastS  Z   QUWZ =
    let  ⟨ z00  , z01 ,•,     z11 ⟩  = Z      -- every matrix |Z|
         ( p00  , p01 , _ ,   p11)   = QUWZ   -- which satisfies |(QU W Z)|
         q10      = identityˡs zers
         q00      = closureIsLeast z00 p00    -- is bigger than |C = fun entireQStep W|
         q11      = closureIsLeast z11 p11
         vs01     = completionIsLeast _ _ _ z01 p01
         mono01   = completionMono q00 (≃sTo≤s refls) q11
    in  (  q00  , ≤s-trans mono01 vs01
        ,  q10  , q11 )

                                                  -- \structure{4.6}{Lifting the proof of |L|}
  entireLS : ∀ (A : U) (Y : S) (B : U) → ∃ (\ X → Y +S (A U*S X +S X S*U B) ≃S X)
  entireLS A Y B = X , proof where
    X : S
    X = _    -- filled in by unification with |Y +S (U2S A *S X +S X *S U2S B)|
    proof : Y +S (U2S A *S X +S X *S U2S B) ≃S X
    open EqReasoning (SemiNearRing2.sSetoid SNR2)
    proof =  -- continued below to fit the width of the paper (it is still in the |where| clause)

      begin
        (Y  +S  (A U*S X  +S  X S*U B) )
      ≡⟨ refl ⟩ -- name the components
        let  ⟨ a00 , a01 ,•, a11 ⟩      = A
             ⟨ b00 , b01 ,•, b11 ⟩      = B
             ⟨ y00 , y01 , y10 , y11 ⟩  = Y
             ⟨ x00 , x01 , x10 , x11 ⟩  = X
        in   Y  +S  (A U*S X  +S  X S*U B)

      ≡⟨ refl ⟩ -- expand |U*S| and |S*U| and use components
        let  AU*SX =  ⟨  a00 u*s x00      +s   a01  *s x10   , a00 u*s x01  +s a01    *s x11
                      ,  zers *s x00      +s   a11 u*s x10   , zers *s x01  +s a11   u*s x11 ⟩
             XS*UB =  ⟨  x00 s*u b00      +s   x01 *s zers   , x00 *s b01   +s x01   s*u b11
                      ,  x10 s*u b00      +s   x11 *s zers   , x10 *s b01   +s x11   s*u b11 ⟩
        in   Y +S (AU*SX  +S  XS*UB)

      ≡⟨ refl ⟩ -- Expand |≃S|, |+S| and collect components
        ⟨  y00   +s ( (a00   u*s  x00   +s   a01  *s x10)  +s (x00 s*u b00   +s x01   *s   zers) )
        ,  y01   +s ( (a00   u*s  x01   +s   a01  *s x11)  +s (x00  *s b01   +s x01  s*u   b11 ) )
        ,  y10   +s ( (zers  *s   x00   +s   a11 u*s x10)  +s (x10 s*u b00   +s x11   *s   zers) )
        ,  y11   +s ( (zers  *s   x01   +s   a11 u*s x11)  +s (x10  *s b01   +s x11  s*u   b11 ) ) ⟩

      ≈⟨ congS zeroLemma00 zeroLemma01 zeroLemma10 zeroLemma11 ⟩
         -- assoc. and comm. of +; zero absorption.
        ⟨  y00 +s a01 *s x10 +s                 (a00 u*s x00 +s x00 s*u b00)
        ,  y01 +s a01 *s x11 +s x00 *s b01 +s   (a00 u*s x01 +s x01 s*u b11)
        ,  y10 +s                               (a11 u*s x10 +s x10 s*u b00)
        ,  y11 +s x10 *s b01 +s                 (a11 u*s x11 +s x11 s*u b11) ⟩

      ≈⟨ congS  completionHasAll completionHasAll completionHasAll  completionHasAll ⟩
        ⟨  x00 , x01 , x10 , x11  ⟩
      ≡⟨ refl ⟩
        X
      ∎

  uniqueLS : SemiNearRing2.UniqueL SNR2           -- \structure{4.7}{Proofs for ordering |L|-solutions}
  uniqueLS (p00 , p01 , p10 , p11) (q00 , q01 , q10 , q11) =  eq00 , eq01 , eq10 , eq11
     where mutual
             s00 = congL (refls <+> (refls <*> sym eq10))
             s11 = congL (refls <+> (sym eq10 <*> refls))
             s01 = congL ((refls <+> (refls <*> sym eq11)) <+> (sym eq00 <*> refls))
             r10 =        trans (sym zeroLemma10) q10
             r00 = s00 (  trans (sym zeroLemma00) q00)
             r11 = s11 (  trans (sym zeroLemma11) q11)
             r01 = s01 (  trans (sym zeroLemma01) q01)
             eq10 = uniqueL (trans (sym zeroLemma10)  p10)  r10
             eq00 = uniqueL (trans (sym zeroLemma00)  p00)  r00
             eq11 = uniqueL (trans (sym zeroLemma11)  p11)  r11
             eq01 = uniqueL (trans (sym zeroLemma01)  p01)  r01

  completionMonoS :  ∀ {a a' y y' b b'} → a ≤U a'  →  y ≤S y'  →  b ≤U b'  →
                     proj₁ (entireLS a y b) ≤S proj₁ (entireLS a' y' b')
  completionMonoS  (p00 , p01 , p10 , p11) (q00 , q01 , q10 , q11)
                   (r00 , r01 , r10 , r11) = m00 , m01 , m10 , m11
     where  m10 = completionMono p11  q10 r00
            m00 = completionMono p00  (q00 [+] p01 [*] m10) r00
            m11 = completionMono p11  (q11 [+] m10 [*] r01) r11
            m01 = completionMono p00  (q01 [+] p01 [*] m11 [+] m00 [*] r01) r11

  congLS : SemiNearRing2.CongL SNR2
  congLS P Q = transS (symS P <+S> reflS) Q

  CSNR : ClosedSemiNearRing
  CSNR = record {
   snr2             = SNR2;
   entireQ          = entireQStep ;
   closureIsLeast   = closureIsLeastS ;
   entireL          = entireLS;
   uniqueL          = uniqueLS ;
   congL            = congLS ;
   completionMono   = completionMonoS }

module Knot where

--  open import Data.Nat
  OneByOne : SemiNearRing -> ClosedSemiNearRing
  OneByOne snr = record {
    snr2            = snr2;

    entireQ          = entireQBase;
    entireL          = entireLBase;
    closureIsLeast   = leastQBase;
    completionMono   = \ _ w<w' _ → w<w';
    uniqueL          = \p q → transs (syms p) (transs (zeroˡʳLemma _ _ _) (transs (syms (zeroˡʳLemma _ _ _)) q));
    congL            = \p q → transs (syms p <+> refls) q

                           }
    where  open SemiNearRing snr using (zers)
           snr2 = record {  snr = snr; u = ⊤;  _+u_ = \ _ _ → tt;
                            u2s = \ _ → zers;  _*u_ = \ _ _ → tt }

           open SemiNearRing snr using (s; _≃s_; refls; _+s_; _*s_; identityˡs; syms; transs; _<+>_)
           open SemiNearRing2 snr2 using (_+u_; _*u_; _≃u_)

           entireQBase : ∀ (w : ⊤) → ∃ \(c : ⊤)  →  w  +u  c *u c  ≃u  c
           entireQBase tt = _ , refls

           open SemiNearRing2 snr2 using (_s*u_; _u*s_)

           open import ZeroLemmas snr             -- \structure{5.1}{Base case for |L|}
           entireLBase : (a : ⊤) (y : s) (b : ⊤) → ∃ (\ x → y +s (a u*s x +s x s*u b) ≃s x)
           entireLBase tt y tt = y , zeroˡʳLemma y y y

           leastQBase = \ _ _ → identityˡs zers   -- \structure{5.2}{Base case for least |Q| }

  open import Data.Nat

  Mat : ℕ → SemiNearRing → ClosedSemiNearRing     -- \structure{6}{Top level recursion for matrices}
  Mat zero     el = OneByOne el
  Mat (suc n)  el = Square (Mat n el)

  Upper : ℕ → SemiNearRing → Set
  Upper n el = ClosedSemiNearRing.u (Mat n el)

                                                  -- \structure{6.1}{Top level algorithm extraction}
  valiantAlgorithm : (el : SemiNearRing) → ∀ n → Upper n el → Upper n el
  valiantAlgorithm el n u = ClosedSemiNearRing.closure (Mat n el) u
