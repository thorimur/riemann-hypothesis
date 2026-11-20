import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
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
open MeasureTheory

namespace GlobalTheory

theorem one_add_pow_le_two_pow_mul_one_add_pow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + a ^ n) := by
        have : 0 ≤ a ^ n := pow_nonneg ha n
        nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) n]
  · calc (1 + a) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow 2 a n
      _ ≤ 2 ^ n * (1 + a ^ n) := by
        have : 0 ≤ (2:ℝ) ^ n := by positivity
        nlinarith

open Real in

theorem fourier_inversion_real_linear_forms :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : SchwartzMap V ℂ),
    ∃ (m : ℕ) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] (V →L[ℝ] ℝ)) (φ : EuclideanSpace ℝ (Fin m) → ℂ),
      Continuous φ ∧ (∀ n : ℕ, Integrable (fun w => (1 + ‖w‖) ^ n * ‖φ w‖)) ∧
      ∀ x, ψ x = ∫ w, φ w * Complex.exp ((A w x : ℂ) * Complex.I) := by
  intro V _ _ _ ψ
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let ψ' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm ψ
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V →L[ℝ] ℝ :=
    (2 * π) • (((ContinuousLinearMap.compL ℝ V _ ℝ).flip (e : V →L[ℝ] _)).comp (innerSL ℝ))
  have hA : ∀ w x, A w x = 2 * π * inner ℝ w (e x) := by
    intro w x
    simp [A]
  let Φ : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ := FourierTransform.fourier ψ'
  refine ⟨Module.finrank ℝ V, A, (Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ),
    Φ.continuous, fun n => ?_, fun x => ?_⟩
  · have hi : Integrable (fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) =>
        2 ^ n * (‖Φ w‖ + ‖w‖ ^ n * ‖Φ w‖)) :=
      ((Φ.integrable_pow_mul volume 0).norm.add (Φ.integrable_pow_mul volume n) |>.congr
        (Filter.Eventually.of_forall fun w => by simp)).const_mul _
    refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + ‖w‖) ^ n * ‖Φ w‖ ≤ 2 ^ n * (1 + ‖w‖ ^ n) * ‖Φ w‖ :=
          mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul_one_add_pow _ (norm_nonneg _) n) (norm_nonneg _)
      _ = 2 ^ n * (‖Φ w‖ + ‖w‖ ^ n * ‖Φ w‖) := by ring
  · have h1 : ψ x = ψ' (e x) := by
      simp [ψ']
    have h2 := congrArg (fun f : SchwartzMap _ ℂ => f (e x))
      (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ) ψ')
    rw [h1, ← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    congr 1
    ext w
    rw [hA, smul_eq_mul, mul_comm]

end GlobalTheory
