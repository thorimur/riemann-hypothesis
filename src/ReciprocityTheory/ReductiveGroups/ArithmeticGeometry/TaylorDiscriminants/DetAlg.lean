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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

namespace ReciprocityTheory.ChartRestriction.G.TB

def DetAlgSt : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K)), I.IsRadical →
    ∀ r : MvPolynomial (Fin n) K ⧸ I,
      (∀ (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
        (φ : (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] L), φ r = 0) → r = 0

theorem detAlg_holds : DetAlgSt := by
  intro K _ n I hI r hr
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [Ideal.Quotient.eq_zero_iff_mem, ← IsJacobsonRing.out inferInstance hI]
  unfold Ideal.jacobson
  rw [Ideal.mem_sInf]
  rintro J ⟨hIJ, hJ⟩
  haveI := hJ
  letI : Field (MvPolynomial (Fin n) K ⧸ J) := Ideal.Quotient.field J
  haveI : Algebra.FiniteType K (MvPolynomial (Fin n) K ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J)
      (Ideal.Quotient.mkₐ_surjective K J)
  haveI : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ J) :=
    finite_of_finite_type_of_isJacobsonRing K _
  have h := hr (MvPolynomial (Fin n) K ⧸ J) (Ideal.Quotient.factorₐ K hIJ)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h

example : (⊥ : Ideal (MvPolynomial (Fin 0) ℚ)).IsRadical := Ideal.isRadical_bot

end ReciprocityTheory.ChartRestriction.G.TB
