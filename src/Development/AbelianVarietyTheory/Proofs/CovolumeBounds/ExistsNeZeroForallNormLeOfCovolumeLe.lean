import Mathlib.Algebra.Module.ZLattice.Covolume
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

open NumberField Module MeasureTheory Metric Set
open scoped Real ENNReal

namespace GlobalTheory

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

set_option backward.isDefEq.respectTransparency.types false in

theorem covolume_eq_relIndex_mul_of_haar (L' L : Submodule ℤ V) [DiscreteTopology L']
    [IsZLattice ℝ L'] [DiscreteTopology L] [IsZLattice ℝ L] (h : L' ≤ L) :
    ZLattice.covolume L' μ =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L μ := by
  classical
  let b : Basis (Fin (finrank ℝ V)) ℤ L := finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)
  let b' : Basis (Fin (finrank ℝ V)) ℤ L' := finBasisOfFinrankEq ℤ L' (ZLattice.rank ℝ L')
  rw [AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b,
    Nat.cast_natAbs, Int.cast_abs,
    ZLattice.covolume_eq_det_mul_measureReal L' μ b' (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)]
  congr 2
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b.ofZLatticeBasis_repr_apply ℝ L ⟨b' j, h (SetLike.coe_mem _)⟩ i)

end Lattice

section Strip

def shearedBox (M ρ y : ℝ) : Set ℂ := {z | |2 * z.re| ≤ M ∧ |2 * z.re * y - z.im| ≤ ρ}

end Strip

section TotallyComplex

open InfinitePlace

end TotallyComplex

section CM

open InfinitePlace IsCMField
open scoped nonZeroDivisors

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

end CM

section Constant

end Constant

section Balls

variable {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℝ (W i)] [∀ i, FiniteDimensional ℝ (W i)]
  [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

end Balls

end GlobalTheory
