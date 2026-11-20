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

namespace Formalism.FourierDecayAlt.K

open Matrix Finset Real

def IsUpUni {K : Type} [Field K] {n : ℕ} (u : Matrix (Fin n) (Fin n) K) : Prop :=
  u.BlockTriangular id ∧ ∀ a, u a a = 1

def w0 {K : Type} [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b => if (a : ℕ) + (b : ℕ) + 1 = n then 1 else 0

def BigCellFree : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (v v' u u' : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    IsUpUni v → IsUpUni v' → IsUpUni u → IsUpUni u' → (∀ a, d a ≠ 0) →
    u * (v * w0 n * Matrix.diagonal d * v') * u' = v * w0 n * Matrix.diagonal d * v' →
    u = 1 ∧ u' = 1

def JointTheoremA : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C' C : ℝ, ∀ (Kx Θ : ℝ) (f r : ℕ) (e σ : ℕ → ℝ),
    4 ≤ Kx → 1 ≤ f → C' ≤ Θ → (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + (C₀ * Θ ^ (-(Kx - 5/2))) ^ f) * √(1 + e i) * σ (i - 1) +
        ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ f) ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2

end Formalism.FourierDecayAlt.K
