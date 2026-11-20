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
import Mathlib.Topology.Sheaves.Presheaf
open MeasureTheory

namespace GlobalTheory

theorem schwartz_clm_bound_finite_seminorm_sum {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (T : SchwartzMap D ℂ →L[ℂ] ℂ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : SchwartzMap D ℂ,
      ‖T φ‖ ≤ C * ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1),
        SchwartzMap.seminorm ℂ m n φ := by
  let q : Seminorm ℂ (SchwartzMap D ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := by
    show Continuous (fun φ => ‖T φ‖)
    exact continuous_norm.comp T.continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ D ℂ) q hq
  refine ⟨s.sup (fun i => max i.1 i.2), (C : ℝ), C.2, fun φ => ?_⟩
  have h1 : ‖T φ‖ = q φ := rfl
  have hnn : ∀ m n, 0 ≤ SchwartzMap.seminorm ℂ m n φ := fun m n => apply_nonneg _ _
  have hsum : 0 ≤ ∑ m ∈ Finset.range (s.sup (fun i => max i.1 i.2) + 1),
      ∑ n ∈ Finset.range (s.sup (fun i => max i.1 i.2) + 1), SchwartzMap.seminorm ℂ m n φ :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ => hnn m n
  have h2 : (s.sup (schwartzSeminormFamily ℂ D ℂ)) φ ≤ ∑ m ∈ Finset.range (s.sup (fun i => max i.1 i.2) + 1),
      ∑ n ∈ Finset.range (s.sup (fun i => max i.1 i.2) + 1), SchwartzMap.seminorm ℂ m n φ := by
    refine Seminorm.finset_sup_apply_le hsum fun i hi => ?_
    have hle : max i.1 i.2 ≤ s.sup (fun i => max i.1 i.2) :=
      Finset.le_sup (f := fun i : ℕ × ℕ => max i.1 i.2) hi
    have hm : i.1 ∈ Finset.range (s.sup (fun i => max i.1 i.2) + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le (le_trans (le_max_left _ _) hle))
    have hn : i.2 ∈ Finset.range (s.sup (fun i => max i.1 i.2) + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le (le_trans (le_max_right _ _) hle))
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    calc SchwartzMap.seminorm ℂ i.1 i.2 φ
        ≤ ∑ n ∈ Finset.range (s.sup (fun i => max i.1 i.2) + 1), SchwartzMap.seminorm ℂ i.1 n φ :=
          Finset.single_le_sum (f := fun n => SchwartzMap.seminorm ℂ i.1 n φ)
            (fun n _ => hnn _ _) hn
      _ ≤ _ := Finset.single_le_sum
            (f := fun m => ∑ n ∈ Finset.range (s.sup (fun i => max i.1 i.2) + 1),
              SchwartzMap.seminorm ℂ m n φ)
            (fun m _ => Finset.sum_nonneg fun n _ => hnn m n) hm
  have h3 : q φ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ D ℂ)) φ := by
    have := hC φ
    simpa [Seminorm.smul_apply, NNReal.smul_def] using this
  rw [h1]
  exact h3.trans (mul_le_mul_of_nonneg_left h2 C.2)

end GlobalTheory
