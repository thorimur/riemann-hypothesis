import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
open Complex Filter Topology
open scoped Real

namespace GlobalTheory

lemma sum_Icc_inv_add_eq_cotTerm (w : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (w + n)⁻¹ =
      1 / w + ∑ j ∈ Finset.range N, (1 / (w - (j + 1)) + 1 / (w + (j + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N:ℤ) + 1)) (insert ((N:ℤ) + 1) (Finset.Icc (-(N:ℤ)) N)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]
    · push_cast
      simp only [one_div, sub_eq_add_neg]
      ring
    · simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_Icc, Finset.mem_insert]; omega

theorem tendsto_sum_Icc_inv_residue_cot :
    ∀ (L : ℕ) (z : ℂ) (r : ℕ), 0 < L → 0 < z.im →
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹) atTop
        (𝓝 (π / L * Complex.cot (π * ((z + r) / L)))) := by
  intro L z r hL hz
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set w : ℂ := (z + r) / L with hw
  have hwL : z + r = w * L := by rw [hw]; field_simp
  have hmem : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hwL
    rw [← hk] at this
    simp at this
    linarith
  have h1 := ((tendsto_logDeriv_euler_cot_sub hmem).const_add (1 / w)).const_mul (L : ℂ)⁻¹
  have hlim : (L : ℂ)⁻¹ * (1 / w + (π * Complex.cot (π * w) - 1 / w)) =
      π / L * Complex.cot (π * w) := by ring
  rw [hlim] at h1
  refine h1.congr fun N => ?_
  have := sum_Icc_inv_add_eq_cotTerm w N
  simp only [cotTerm]
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hwL, ← add_mul, mul_inv, mul_comm]

end GlobalTheory
