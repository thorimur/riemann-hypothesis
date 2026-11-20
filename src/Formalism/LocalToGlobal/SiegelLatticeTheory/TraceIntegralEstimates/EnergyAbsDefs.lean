import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def yv (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) : HH :=
  ∫ z, ∫ s in Ω, ⟪W (s⁻¹ * z), e⟫_ℂ • σ (s⁻¹ * z) w ∂μS ∂ν

def Yop (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) : V →L[ℂ] HH :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ V i)).smulRight (yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i))

theorem Yop_apply (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) :
    Yop μS ν σ w W Ω e =
      ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i) := by
  simp only [Yop, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem Yop_apply_basis (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G)
    (j : Fin (Module.finrank ℂ V)) :
    Yop μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) = yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) := by
  rw [Yop_apply, Finset.sum_eq_single j]
  · rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal]; simp
  · intro i _ hij
    rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal, if_neg hij, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

end Formalism.L2.S.Pv.EnergyAbs
