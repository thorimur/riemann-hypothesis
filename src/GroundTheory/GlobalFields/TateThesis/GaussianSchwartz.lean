import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

open Real Function
open scoped ContDiff Nat SchwartzMap

namespace GroundTheory.Global

noncomputable section

theorem one_add_pow_mul_exp_neg_pi_mul_sq_le {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N ^ 2 / (4 * π)) := by
  have h1 : (1 + r) ^ N ≤ Real.exp (N * r) := by
    calc (1 + r) ^ N ≤ Real.exp r ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp (N * r) := by rw [← Real.exp_nat_mul]
  calc (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N * r) * Real.exp (-π * r ^ 2) := by
        gcongr
    _ = Real.exp (N * r - π * r ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (N ^ 2 / (4 * π)) := by
      apply Real.exp_le_exp.2
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((N : ℝ) - 2 * π * r), Real.pi_pos]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussianFun (x : E) : ℂ := ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)

theorem contDiff_gaussianFun : ContDiff ℝ ∞ (gaussianFun (E := E)) :=
  Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem norm_iteratedFDeriv_gaussian_le (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (gaussianFun (E := E)) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (-π * ‖x‖ ^ 2) := by
  set q : E → ℝ := fun x ↦ -π * ‖x‖ ^ 2 with hq_def
  have hq : q.HasTemperateGrowth := (HasTemperateGrowth.const (-π)).mul (hasTemperateGrowth_norm_sq E)
  have hqs : ContDiff ℝ ∞ q := contDiff_const.mul (contDiff_norm_sq ℝ)
  obtain ⟨k, C, hC, hb⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * max C 1 ^ n, k * n, by positivity, fun x ↦ ?_⟩
  have hx1 : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg x])
  set D := max C 1 * (1 + ‖x‖) ^ k
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hx1
  have hcomp : ‖iteratedFDeriv ℝ n (Real.exp ∘ q) x‖ ≤ n ! * Real.exp (q x) * D ^ n := by
    refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hqs (by exact_mod_cast le_top) x
      (fun i _ ↦ (norm_iteratedFDeriv_exp i (q x)).le) fun i hi1 hin ↦ ?_
    calc ‖iteratedFDeriv ℝ i q x‖ ≤ C * (1 + ‖x‖) ^ k := hb i hin x
      _ ≤ D := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
  have hG : gaussianFun (E := E) = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (Real.exp ∘ q) := rfl
  rw [hG, LinearIsometry.norm_iteratedFDeriv_comp_left _
    (Real.contDiff_exp.comp hqs).contDiffAt (by exact_mod_cast le_top)]
  refine hcomp.trans (le_of_eq ?_)
  simp only [D, mul_pow, ← pow_mul, hq_def]
  ring

def gaussianSchwartz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : 𝓢(E, ℂ) where
  toFun := gaussianFun
  smooth' := contDiff_gaussianFun
  decay' k n := by
    obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_gaussian_le (E := E) n
    refine ⟨C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n gaussianFun x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ j * Real.exp (-π * ‖x‖ ^ 2)) :=
          mul_le_mul hk (hb x) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (-π * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_neg_pi_mul_sq_le (norm_nonneg x) _) hC

@[simp]
theorem gaussianSchwartz_apply (x : E) :
    gaussianSchwartz E x = ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
  rfl

end

end GroundTheory.Global
