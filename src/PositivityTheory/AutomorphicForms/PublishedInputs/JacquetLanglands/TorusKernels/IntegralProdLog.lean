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
import Mathlib.MeasureTheory.Integral.Pi
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

noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

theorem integral_prod_log {I : Type} [Fintype I] [Nontrivial I] (φ : I → ℝ → ℂ)
    (h : ∀ v, Integrable (φ v) ∧ Integrable (fun x => (Real.log (1 + x ^ 2) : ℂ) * φ v x) ∧ ∫ x, φ v x = 0)
    (R C : ℝ) :
    ∫ x : I → ℝ, (∏ v, φ v (x v)) * ((R * (C + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ) = 0 := by
  classical
  set ψ : I → I → ℝ → ℂ := fun w v t =>
    (if v = w then (Real.log (1 + t ^ 2) : ℂ) else 1) * φ v t with hψ
  have hψprod : ∀ (w : I) (x : I → ℝ),
      ∏ v, ψ w v (x v) = (Real.log (1 + x w ^ 2) : ℂ) * ∏ v, φ v (x v) := by
    intro w x
    simp only [hψ, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hψint : ∀ w v, Integrable (ψ w v) := by
    intro w v
    by_cases hv : v = w
    · simpa [hψ, hv] using (h w).2.1
    · simpa [hψ, hv] using (h v).1
  have hP : Integrable (fun x : I → ℝ => ∏ v, φ v (x v)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun v => (h v).1)
  have hψP : ∀ w, Integrable (fun x : I → ℝ => ∏ v, ψ w v (x v)) := by
    intro w
    rw [volume_pi]
    exact Integrable.fintype_prod (fun v => hψint w v)
  have hφzero : ∫ x : I → ℝ, ∏ v, φ v (x v) = 0 := by
    obtain ⟨v, -, -⟩ := exists_pair_ne I
    rw [integral_fintype_prod_volume_eq_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (h v).2.2
  have hψzero : ∀ w, ∫ x : I → ℝ, ∏ v, ψ w v (x v) = 0 := by
    intro w
    obtain ⟨v, hv⟩ := exists_ne w
    rw [integral_fintype_prod_volume_eq_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    simpa [hψ, hv] using (h v).2.2
  have key : ∀ x : I → ℝ,
      (∏ v, φ v (x v)) * ((R * (C + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ)
        = (R * C : ℂ) * ∏ v, φ v (x v) + ∑ w, (R : ℂ) * ∏ v, ψ w v (x v) := by
    intro x
    simp only [hψprod]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    push_cast
    ring
  simp_rw [key]
  rw [integral_add (hP.const_mul _) (integrable_finset_sum _ fun w _ => (hψP w).const_mul _),
    integral_const_mul, hφzero,
    integral_finset_sum _ fun w _ => (hψP w).const_mul _]
  simp [integral_const_mul, hψzero]

end UpperTheory.Esk.UnipotentIntegrandLemmas
