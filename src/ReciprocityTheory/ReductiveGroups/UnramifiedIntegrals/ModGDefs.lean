import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.WittVector.IsPoly
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

noncomputable section
open scoped BigOperators Classical
open NumberField IsDedekindDomain Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def sqD (d : ℕ) : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ)

theorem sqD_sq (d : ℕ) : sqD d ^ 2 = -(d : ℂ) := by
  unfold sqD
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

def KQ (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {sqD d}

theorem sqD_isIntegral (d : ℕ) : IsIntegral ℚ (sqD d) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [sqD_sq]

scoped instance KQ_numberField (d : ℕ) : NumberField (KQ d) where
  to_charZero := inferInstance
  to_finiteDimensional := IntermediateField.adjoin.finiteDimensional (sqD_isIntegral d)

def sqK (d : ℕ) : KQ d := ⟨sqD d, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

abbrev Om (d : ℕ) : IntermediateField (KQ d) ℂ := algebraicClosure (KQ d) ℂ

def Aio (d l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) : ValuationSubring (Om d) :=
  ((NormedField.valuation (K := ℂ_[l])).valuationSubring).comap
    ((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ))

def InertiaEl {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) : Prop :=
  g ∈ A.decompositionSubgroup E ∧ ∀ x ∈ A, g x - x ∈ A.nonunits

end ReciprocityTheory.ChartRestriction.L1
