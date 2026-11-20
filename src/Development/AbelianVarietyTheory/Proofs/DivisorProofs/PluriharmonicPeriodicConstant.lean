import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem periodic_const_of_holomorphic_differential
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : V → ℝ) (K Λ : Set V)
    (hf : ContDiff ℝ 1 f)
    (hhol : ∀ a : V, Differentiable ℂ (fun z => ((fderiv ℝ f z a : ℝ) : ℂ) - Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ)))
    (hK : IsCompact K) (hper : ∀ l ∈ Λ, ∀ z, f (z + l) = f z)
    (hcov : ∀ z, ∃ k ∈ K, ∃ l ∈ Λ, z = k + l) : ∀ z, f z = f 0 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hperd : ∀ l ∈ Λ, ∀ z, fderiv ℝ f (z + l) = fderiv ℝ f z := by
    intro l hl z
    have h1 : (fun w => f (w + l)) = f := funext fun w => hper l hl w
    have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := z) l
    rw [h1] at h2
    exact h2.symm
  have hperd' : ∀ z, ∃ k ∈ K, fderiv ℝ f z = fderiv ℝ f k := by
    intro z
    obtain ⟨k, hk, l, hl, rfl⟩ := hcov z
    exact ⟨k, hk, hperd l hl k⟩
  have hconst : ∀ z, fderiv ℝ f z = fderiv ℝ f 0 := by
    intro z
    ext a
    set φ : V → ℂ := fun z => ((fderiv ℝ f z a : ℝ) : ℂ) - Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ) with hφ
    have hφc : Continuous φ := by
      have h1 : Continuous fun z => fderiv ℝ f z a := hcd.clm_apply continuous_const
      have h2 : Continuous fun z => fderiv ℝ f z (Complex.I • a) := hcd.clm_apply continuous_const
      exact (Complex.continuous_ofReal.comp h1).sub (continuous_const.mul (Complex.continuous_ofReal.comp h2))
    have hbd : Bornology.IsBounded (Set.range φ) := by
      refine ((hK.image hφc).isBounded).subset ?_
      rintro _ ⟨w, rfl⟩
      obtain ⟨k, hk, hkw⟩ := hperd' w
      exact ⟨k, hk, by simp only [hφ, hkw]⟩
    have hL := (hhol a).apply_eq_apply_of_bounded hbd z 0
    have := congrArg Complex.re hL
    simpa [hφ] using this
  have hne : K.Nonempty := by
    obtain ⟨k, hk, _, _, _⟩ := hcov 0
    exact ⟨k, hk⟩
  obtain ⟨z₀, -, hmax⟩ := hK.exists_isMaxOn hne hd.continuous.continuousOn
  have hglob : IsLocalMax f z₀ := by
    refine Filter.Eventually.of_forall fun z => ?_
    obtain ⟨k, hk, l, hl, rfl⟩ := hcov z
    rw [hper l hl k]
    exact hmax hk
  have h0 : ∀ z, fderiv ℝ f z = 0 := by
    intro z
    rw [hconst z, ← hconst z₀]
    exact hglob.fderiv_eq_zero
  intro z
  exact is_const_of_fderiv_eq_zero hd h0 z 0

end GlobalTheory
