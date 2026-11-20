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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK

set_option backward.isDefEq.respectTransparency false in

theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  have hF : Measurable fun x : (i : _) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  by_cases hne : Nonempty ((i : _) → E i)
  · obtain ⟨x0⟩ := hne
    have key : ∀ s : Finset _, ∀ x : (i : _) → E i,
        lmarginal μ s (fun x : (i : _) → E i => ∏ i, f i (x i)) x =
          ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro x
        simp [lmarginal_empty]
      | insert a s ha ih =>
        intro x
        rw [lmarginal_insert _ hF ha]
        simp_rw [ih]
        have hC : ∀ t, ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (Function.update x a t i)) =
            f a t * ∏ i ∈ Finset.univ.erase a, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
          intro t
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [ha]
          · refine Finset.prod_congr rfl fun i hi => ?_
            simp [Function.update_apply, Finset.ne_of_mem_erase hi]
        simp_rw [hC]
        rw [lintegral_mul_const _ (hf a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
        congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi]
    rw [lintegral_eq_lmarginal_univ x0, key]
    simp
  · have hj : ∃ j, IsEmpty (E j) := by
      by_contra h
      push_neg at h
      exact hne ⟨fun i => (h i).some⟩
    obtain ⟨j, hj⟩ := hj
    haveI : IsEmpty ((i : _) → E i) := not_nonempty_iff.1 hne
    rw [lintegral_of_isEmpty]
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    haveI := hj
    exact lintegral_of_isEmpty _ _

theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  have hF : Measurable fun x : (i : _) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  by_cases hne : Nonempty ((i : _) → E i)
  · obtain ⟨x0⟩ := hne
    have key : ∀ s : Finset _, ∀ x : (i : _) → E i,
        lmarginal μ s (fun x : (i : _) → E i => ∏ i, f i (x i)) x =
          ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro x
        simp [lmarginal_empty]
      | insert a s ha ih =>
        intro x
        rw [lmarginal_insert _ hF ha]
        simp_rw [ih]
        have hC : ∀ t, ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (Function.update x a t i)) =
            f a t * ∏ i ∈ Finset.univ.erase a, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
          intro t
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [ha]
          · refine Finset.prod_congr rfl fun i hi => ?_
            simp [Function.update_apply, Finset.ne_of_mem_erase hi]
        simp_rw [hC]
        rw [lintegral_mul_const _ (hf a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
        congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi]
    rw [lintegral_eq_lmarginal_univ x0, key]
    simp
  · have hj : ∃ j, IsEmpty (E j) := by
      by_contra h
      push_neg at h
      exact hne ⟨fun i => (h i).some⟩
    obtain ⟨j, hj⟩ := hj
    haveI : IsEmpty ((i : _) → E i) := not_nonempty_iff.1 hne
    rw [lintegral_of_isEmpty]
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    haveI := hj
    exact lintegral_of_isEmpty _ _

end QPK
