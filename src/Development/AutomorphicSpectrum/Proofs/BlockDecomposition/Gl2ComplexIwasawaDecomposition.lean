import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.GodementFE.Iwasawa

theorem gl2_complex_iwasawa :
    ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.det ≠ 0 → ∃ (κ : Matrix (Fin 2) (Fin 2) ℂ) (b : ℂ) (R : ℝ),
    0 < R ∧ R ^ 2 = ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 ∧ κ * κᴴ = 1 ∧ ‖κ.det‖ = 1 ∧
      g = !![g.det / (R : ℂ), b; 0, (R : ℂ)] * κ := by
  intro g hg
  have hdet : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
  have hS : 0 < ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 := by
    by_contra hcon
    have h0 : ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 ≤ 0 := not_lt.mp hcon
    have h1 : ‖g 1 0‖ = 0 := by nlinarith [norm_nonneg (g 1 0), norm_nonneg (g 1 1), sq_nonneg ‖g 1 0‖, sq_nonneg ‖g 1 1‖]
    have h2 : ‖g 1 1‖ = 0 := by nlinarith [norm_nonneg (g 1 0), norm_nonneg (g 1 1), sq_nonneg ‖g 1 0‖, sq_nonneg ‖g 1 1‖]
    apply hg
    rw [hdet, norm_eq_zero.mp h1, norm_eq_zero.mp h2]
    ring
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = Real.sqrt (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) := ⟨_, rfl⟩
  have hRpos : 0 < R := hRdef ▸ Real.sqrt_pos.mpr hS
  have hR2 : R ^ 2 = ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 := by
    rw [hRdef]; exact Real.sq_sqrt hS.le
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hsum : g 1 0 * (starRingEnd ℂ) (g 1 0) + g 1 1 * (starRingEnd ℂ) (g 1 1) = (R : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact_mod_cast hR2.symm
  generalize hc : g 1 0 = c at *
  generalize hd : g 1 1 = d at *
  generalize ha : g 0 0 = a at *
  generalize hb : g 0 1 = b at *
  generalize hcc : (starRingEnd ℂ) c = c' at *
  generalize hdc : (starRingEnd ℂ) d = d' at *
  refine ⟨!![d' / R, -c' / R; c / R, d / R], (a * c' + b * d') / R, R, hRpos, hR2, ?_, ?_, ?_⟩
  · have e1 : (starRingEnd ℂ) d' = d := by rw [← hdc, Complex.conj_conj]
    have e2 : (starRingEnd ℂ) c' = c := by rw [← hcc, Complex.conj_conj]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, e1, e2, hcc, hdc] <;>
      field_simp <;> first | ring1 | linear_combination hsum
  · have : (!![d' / R, -c' / R; c / R, d / R] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
      rw [Matrix.det_fin_two_of]
      field_simp
      linear_combination hsum
    rw [this]; simp
  · rw [hdet]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc, hd] <;>
      field_simp <;> first | ring1 | linear_combination a * hsum | linear_combination (-a) * hsum | linear_combination b * hsum | linear_combination (-b) * hsum | linear_combination hsum | linear_combination (-1 : ℂ) * hsum

end GlobalTheory.CompanionTheory.GodementFE.Iwasawa
