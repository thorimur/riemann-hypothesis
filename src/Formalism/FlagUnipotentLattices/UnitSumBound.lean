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

open Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def UnitSumBound : Prop :=
  ∀ (V ι : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (s : Finset ι) (a : ι → ℂ)
    (x : ι → V) (w B : ℝ), 0 ≤ w → (∀ i ∈ s, w * ‖x i‖ ^ 2 ≤ B) →
    w * ‖∑ i ∈ s, a i • x i‖ ^ 2 ≤ B * (∑ i ∈ s, ‖a i‖) ^ 2

def volU (j : ℕ) : ℝ := ∏ i ∈ Icc 1 j, (2 * Real.pi) ^ i / ((i - 1).factorial : ℝ)

def VolStep : Prop :=
  ∀ j : ℕ, volU j / volU (j + 1) = (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1)

def VolRatio : Prop :=
  ∀ k p : ℕ, volU (k + p) / volU k * ∏ i ∈ Ico k (k + p), (i.factorial : ℝ) =
    (2 * Real.pi) ^ (p * k + p * (p + 1) / 2)

def ConstProduct : Prop :=
  ∀ (j r : ℕ) (T T' g v n0 κ dimpi Vd VV : ℝ), 0 < T → 0 < T' → 0 < g → 0 < v → VV ≠ 0 →
    n0 * (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1) =
      κ / (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) →
    n0 * (T * T') ^ j *
      (dimpi * (Vd / ∏ i ∈ range (j + 1), (i.factorial : ℝ)) * volU (j + 1 + (2 * r + 1)) * volU j /
        (VV / (∏ i ∈ range (j + 1 + (2 * r + 1)), (i.factorial : ℝ)) * volU (j + 1) ^ 2 *
          (2 * v) ^ (2 * r * (j + 1)))) =
      dimpi * (T' / g ^ (2 * r + 2) * (Real.pi / v) ^ (2 * r + 1)) ^ (j + 1) * (Vd / VV) *
        (κ * (2 * Real.pi) ^ ((2 * r + 1) * (2 * r + 2) / 2) / (T * T'))

def TcritForm : Prop :=
  ∀ (k r : ℕ) (T' g v rd Vd VV Tc : ℝ), 0 < T' → 0 < g → 0 < v → 0 < rd → Vd ≠ 0 → VV ≠ 0 →
    0 < Tc →
    Tc ^ k * ((Real.pi / v) ^ ((2 * r + 1) * k + (2 * r + 2) * (2 * r + 1) / 2) *
        rd ^ (((2 * r + 1 : ℕ) : ℝ) / 2)) =
      g ^ (k * (2 * r + 2) + (2 * r + 2) * (2 * r + 1) / 2) * (VV / Vd) →
    (T' / g ^ (2 * r + 2) * (Real.pi / v) ^ (2 * r + 1)) ^ k * (Vd / VV) =
      (Tc / T')⁻¹ ^ k *
        ((g / (Real.pi / v)) ^ ((2 * r + 2) * (2 * r + 1) / 2) / rd ^ (((2 * r + 1 : ℕ) : ℝ) / 2))

def PlaceRoot : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (x y : ι → ℝ) (K B₁ B₂ : ℝ), 0 ≤ K → 0 ≤ B₁ → 0 ≤ B₂ →
    (∀ v, 0 < y v) → (∀ v, x v = K * y v) →
    B₁ ^ Fintype.card ι * ∏ v, y v ≤ ∏ v, x v → ∏ v, x v ≤ B₂ ^ Fintype.card ι * ∏ v, y v →
    ∀ v, B₁ * y v ≤ x v ∧ x v ≤ B₂ * y v

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
