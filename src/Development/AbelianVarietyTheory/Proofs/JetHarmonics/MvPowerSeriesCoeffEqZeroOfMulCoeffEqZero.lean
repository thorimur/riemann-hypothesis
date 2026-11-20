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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Monotonicity.Lemmas
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

namespace GlobalTheory

theorem mvPowerSeries_coeff_eq_zero_of_mul_coeff_eq_zero :
    ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (h : MvPowerSeries σ F), h ≠ 0 → ∃ k : ℕ, ∀ (m : ℕ) (u : MvPowerSeries σ F), (∀ e : σ →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e (h * u) = 0) → ∀ e : σ →₀ ℕ, e.degree + k ≤ m → MvPowerSeries.coeff e u = 0 := by
  intro F _ σ _ h hh
  have hfin : h.order ≠ ⊤ := fun ht => hh (MvPowerSeries.order_eq_top_iff.mp ht)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨k, fun m u hu e he => ?_⟩
  by_contra hne
  have h1 : u.order ≤ (e.degree : ℕ∞) := MvPowerSeries.order_le hne
  have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ (h * u).order :=
    MvPowerSeries.nat_le_order fun d hd => hu d (Nat.lt_succ_iff.mp hd)
  rw [MvPowerSeries.order_mul, ← hk] at h2
  have h3 : ((m + 1 : ℕ) : ℕ∞) ≤ ((k + e.degree : ℕ) : ℕ∞) := by
    refine h2.trans ?_
    rw [Nat.cast_add]
    exact add_le_add le_rfl h1
  have h4 : m + 1 ≤ k + e.degree := by exact_mod_cast h3
  omega

end GlobalTheory
