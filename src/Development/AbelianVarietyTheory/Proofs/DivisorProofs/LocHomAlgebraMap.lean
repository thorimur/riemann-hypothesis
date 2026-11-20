import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

variable (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D]

noncomputable def toNorm : integralClosure S L →+* integralClosure D (TensorProduct S D L) :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).toRingHom.comp
      (integralClosure S L).val.toRingHom)
    (integralClosure D (TensorProduct S D L)) (fun o => by
      have h : IsIntegral S (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L) (o : L)) :=
        o.2.map _
      exact h.tower_top)

@[simp] theorem toNorm_coe (o : integralClosure S L) :
    ((toNorm S L D o : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) =
      (1 : D) ⊗ₜ[S] (o : L) := rfl

variable {S L D}

noncomputable def locHom (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsPrime] :
    Localization.AtPrime (Q.comap (toNorm S L D)) →+* Localization.AtPrime Q :=
  IsLocalization.lift (M := (Q.comap (toNorm S L D)).primeCompl)
    (g := (algebraMap _ (Localization.AtPrime Q)).comp (toNorm S L D)) (fun s =>
      IsLocalization.map_units (Localization.AtPrime Q) (⟨toNorm S L D s, s.2⟩ : Q.primeCompl))

theorem locHom_algebraMap (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsPrime]
    (o : integralClosure S L) :
    locHom Q (algebraMap _ _ o) = algebraMap _ (Localization.AtPrime Q) (toNorm S L D o) :=
  IsLocalization.lift_eq _ _

end GlobalTheory.AbhyankarLocal
