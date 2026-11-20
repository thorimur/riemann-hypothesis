import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Star
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

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_max_ratio_cleared :
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ι → ℤ) (m : ι → ℕ), (∀ i, 0 < m i) →
      ∃ (M : ℕ) (a : ℤ) (i₀ : ι), 0 < M ∧ (∀ i, (M : ℤ) * n i ≤ a * m i) ∧
        (M : ℤ) * n i₀ = a * m i₀ := by
  intro ι _ _ n m hm
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (n i : ℚ) / m i) Finset.univ_nonempty
  refine ⟨m i₀, n i₀, i₀, hm i₀, fun i => ?_, mul_comm _ _⟩
  have h := hi₀ i (Finset.mem_univ i)
  have hmi : (0 : ℚ) < m i := by exact_mod_cast hm i
  have hm0 : (0 : ℚ) < m i₀ := by exact_mod_cast hm i₀
  rw [div_le_div_iff₀ hmi hm0] at h
  have hq : (m i₀ : ℚ) * n i ≤ n i₀ * (m i : ℚ) := by linarith
  exact_mod_cast hq

end GlobalTheory.CompanionTheory.Ar.Flat
