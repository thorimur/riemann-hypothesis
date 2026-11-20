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

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def BasisChange : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (J m N : ℕ)
    (lam : Fin J → Fin N → K) (y : Fin m → Fin N → K),
    (∀ i a, ‖lam i a‖ ≤ 1) → (∀ k a, ‖y k a‖ ≤ 1) →
    ∀ e : Fin J → Fin m, Function.Injective e →
    ‖(Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a).det‖ = 1 →
    ∃ T : Matrix (Fin m) (Fin m) K, (∀ k k', ‖T k k'‖ ≤ 1) ∧ ‖T.det‖ = 1 ∧
      ∀ i k, (∑ a, lam i a * ∑ k', T k k' * y k' a) = if k = e i then 1 else 0

def DegProd : Prop :=
  ∀ (R : Type u) [CommRing R] (σ κ : Type) [DecidableEq κ] (blk : σ → Option κ) (n : ℕ)
    (f : Fin n → MvPolynomial σ R) (bd : Fin n → ℕ),
    (∀ c, ∀ mono ∈ (f c).support, ∀ k : κ,
      (mono.support.filter (fun v => blk v = some k)).sum mono ≤ bd c) →
    ∀ mono ∈ (∏ c, f c).support, ∀ k : κ,
      (mono.support.filter (fun v => blk v = some k)).sum mono ≤ ∑ c, bd c

def MinorDegAll : Prop :=
  ∀ (R : Type u) [CommRing R] (m p : ℕ) (T : Fin p → Fin m → R),
    ∀ mono ∈ (Matrix.of fun (i c : Fin p) =>
        (∑ k, MvPolynomial.C (T i k) * MvPolynomial.X (k, c) : MvPolynomial (Fin m × Fin p) R)).det.support,
      ∀ k : Fin m, (∑ c : Fin p, mono (k, c)) ≤ 1

def JCount : Prop :=
  ∀ l a : ℕ, 2 ≤ l → 1 ≤ a →
    (((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℝ) ≤
      2 * Real.logb l a + 1

end Formalism.DworkPowerSeriesWeights
