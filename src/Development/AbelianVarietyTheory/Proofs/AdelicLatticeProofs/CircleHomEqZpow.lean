import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.AddCircle
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

open scoped Topology

namespace GlobalTheory

open MeasureTheory AddCircle in

theorem circle_hom_eq_zpow :
    ∀ f : Circle →* Circle, Continuous f → ∃ n : ℤ, ∀ z, f z = z ^ n := by
  intro f hf
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => (f (toCircle x) : ℂ),
      continuous_subtype_val.comp (hf.comp continuous_toCircle)⟩
  have hg : ∀ x, g x = (f (toCircle x) : ℂ) := fun _ => rfl
  have hex : ∃ n : ℤ, fourierCoeff g n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : fourierCoeff g = fun _ => 0 := funext hcon
    have hs := has_pointwise_sum_fourier_series_of_summable (f := g)
      (by rw [h0]; exact summable_zero) 0
    simp only [hcon, zero_smul] at hs
    have := hs.unique hasSum_zero
    rw [hg] at this
    exact Circle.coe_ne_zero _ this
  obtain ⟨n, hn⟩ := hex
  refine ⟨n, fun z => ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w : AddCircle (1 : ℝ), toCircle w = z := by
    obtain ⟨w, hw⟩ := (homeomorphCircle (T := 1) one_ne_zero).surjective z
    exact ⟨w, by rw [← homeomorphCircle_apply one_ne_zero, hw]⟩
  have key : fourierCoeff g n = (fourier (-n) w * g w) * fourierCoeff g n := by
    unfold fourierCoeff
    rw [← integral_const_mul]
    rw [← integral_add_left_eq_self (μ := haarAddCircle)
      (fun t : AddCircle (1 : ℝ) => fourier (-n) t • g t) w]
    congr 1
    ext t
    simp only [hg, fourier_apply, zsmul_add, toCircle_add, map_mul, Circle.coe_mul, smul_eq_mul]
    ring
  have h1 : fourier (-n) w * g w = 1 := by
    have := mul_right_cancel₀ hn (key.symm.trans (one_mul _).symm)
    exact this
  rw [hg, fourier_apply, toCircle_zsmul, ← Circle.coe_mul, ← Circle.coe_one] at h1
  have h2 : toCircle w ^ (-n) * f (toCircle w) = (1 : Circle) := Circle.ext h1
  rw [zpow_neg, inv_mul_eq_one] at h2
  exact h2.symm

end GlobalTheory
