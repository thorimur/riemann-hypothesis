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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.IntegralAlgebraMapNormBound

open Polynomial

lemma norm_algebraMap_le_one {l : ℕ} [Fact (Nat.Prime l)] (c : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) c‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  have h1 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] c)‖
      = ‖algebraMap ℤ_[l] ℚ_[l] c‖ := PadicAlgCl.norm_extends l _
  rw [h1]
  exact PadicInt.norm_le_one c

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hmon, hp⟩ := hx
  set n := p.natDegree with hn
  have hx0 : 0 < ‖x‖ := lt_trans one_pos hlt
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, ← hn] at hp
  have hlead : p.coeff n = 1 := hmon
  rw [hlead, map_one, one_mul] at hp
  have heq : x ^ n = -∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hp
  have hbound : ‖∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ n / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, le_div_iff₀ hx0]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i * ‖x‖
        ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact norm_algebraMap_le_one _
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ ‖x‖ ^ n := pow_le_pow_right₀ hlt.le (by omega)
  have hxn : ‖x‖ ^ n ≤ ‖x‖ ^ n / ‖x‖ := by
    calc ‖x‖ ^ n = ‖x ^ n‖ := (norm_pow x n).symm
      _ = _ := by rw [heq, norm_neg]
      _ ≤ _ := hbound
  have hpos : 0 < ‖x‖ ^ n := pow_pos hx0 n
  have : ‖x‖ ^ n / ‖x‖ < ‖x‖ ^ n := div_lt_self hpos hlt
  linarith

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l),
    IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) :=
  fun x hx => norm_le_one_of_isIntegral x hx

end GlobalTheory.IntegralAlgebraMapNormBound
