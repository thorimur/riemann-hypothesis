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

open MeasureTheory Module Metric Set
open scoped Pointwise

noncomputable section

namespace Formalism.FN

def succMin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) (K : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K))}

def succMinBall {r : ℕ} (R : Submodule ℤ (EuclideanSpace ℝ (Fin r))) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧
    i ≤ Module.finrank ℝ (Submodule.span ℝ ((R : Set (EuclideanSpace ℝ (Fin r))) ∩ Metric.closedBall 0 t))}

def MinkowskiIIUpper : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
      μ.real K * ∏ i : Fin (finrank ℝ E), succMin L K ((i : ℕ) + 1)
        ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ

def MinkowskiIILower : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
      (2 : ℝ) ^ finrank ℝ E / (Nat.factorial (finrank ℝ E) : ℝ) * ZLattice.covolume L μ
        ≤ μ.real K * ∏ i : Fin (finrank ℝ E), succMin L K ((i : ℕ) + 1)

def MinkowskiIIBall : Prop :=
  ∀ (r : ℕ) (R : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology R] [IsZLattice ℝ R],
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) 1)).toReal *
        ∏ i : Fin r, succMinBall R ((i : ℕ) + 1)
      ≤ 2 ^ r * ZLattice.covolume R

end Formalism.FN
