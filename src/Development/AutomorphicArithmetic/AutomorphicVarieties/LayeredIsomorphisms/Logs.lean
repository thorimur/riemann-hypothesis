import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
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

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.logs :
    (∀ (l : ℕ) (J Ct X x : ℝ), 2 ≤ l → 0 < J → 0 ≤ Ct → 1 ≤ X → X ^ (1 / J) ≤ x →
        ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * Ct * J * Real.log x) ∧
      (∀ (J eps X x : ℝ), 0 < J → 0 < eps → 1 ≤ X → X ^ (1 / J) ≤ x → X ^ (eps / (4 * J)) ≤ x ^ (eps / 4)) ∧
      (∀ (e : ℕ) (A1 x : ℝ), 1 ≤ x → (2 : ℝ) ^ e ≤ x ^ A1 → (e : ℝ) + 2 ≤ (2 * |A1| + 2) * (1 + Real.log x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l J Ct X x hl hJ hCt hX hx
    have hX0 : 0 < X := by linarith
    have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hX (by positivity)) hx
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlogX : Real.log X ≤ J * Real.log x := by
      have h1 : Real.log (X ^ (1 / J)) ≤ Real.log x :=
        Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hx
      rw [Real.log_rpow hX0] at h1
      have h2 : J * ((1 / J) * Real.log X) = Real.log X := by field_simp
      calc Real.log X = J * ((1 / J) * Real.log X) := h2.symm
        _ ≤ J * Real.log x := mul_le_mul_of_nonneg_left h1 hJ.le
    have hl2 : (1:ℝ) / 2 < Real.log l := by
      have h3 : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) (by exact_mod_cast hl)
      have h4 := Real.log_two_gt_d9
      linarith
    rcases Nat.eq_zero_or_pos ⌊X ^ Ct⌋₊ with h0 | hpos
    · rw [h0, Nat.log_zero_right, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCt) hJ.le) hlogx
    · have hpow : (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ X ^ Ct := by
        have h1 : l ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ ⌊X ^ Ct⌋₊ := Nat.pow_log_le_self l hpos.ne'
        have h2 : ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ X ^ Ct := Nat.floor_le (Real.rpow_nonneg hX0.le _)
        calc (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) = ((l ^ (Nat.log l ⌊X ^ Ct⌋₊) : ℕ) : ℝ) :=
              (Nat.cast_pow l _).symm
          _ ≤ ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ X ^ Ct := h2
      have hl0 : (0:ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      have hlog := Real.log_le_log (pow_pos hl0 _) hpow
      rw [Real.log_pow, Real.log_rpow hX0] at hlog
      have hk0 : (0:ℝ) ≤ (Nat.log l ⌊X ^ Ct⌋₊ : ℕ) := Nat.cast_nonneg _
      have hk : ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * (((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) * Real.log l) := by
        nlinarith [mul_le_mul_of_nonneg_left hl2.le hk0]
      nlinarith [mul_le_mul_of_nonneg_left hlogX hCt]
  · intro J eps X x hJ heps hX hx
    have hX0 : 0 ≤ X := by linarith
    have h1 : X ^ (eps / (4 * J)) = (X ^ (1 / J)) ^ (eps / 4) := by
      rw [← Real.rpow_mul hX0]
      congr 1
      field_simp
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hx (by positivity)
  · intro e A1 x hx h
    have hx0 : 0 < x := by linarith
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_rpow hx0] at hlog
    have h2 := Real.log_two_gt_d9
    have habs : A1 * Real.log x ≤ |A1| * Real.log x :=
      mul_le_mul_of_nonneg_right (le_abs_self A1) hlogx
    have he0 : (0:ℝ) ≤ e := Nat.cast_nonneg e
    have he : (e:ℝ) ≤ 2 * (e * Real.log 2) := by nlinarith
    nlinarith [abs_nonneg A1, mul_nonneg (abs_nonneg A1) hlogx]
