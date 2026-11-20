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
open MeasureTheory Set
open scoped ContDiff

namespace GlobalTheory

theorem integral_unitCube_pos_of_periodic :
    ∀ (ι : Type) [Fintype ι] (f : (ι → ℝ) → ℝ), Continuous f → (∀ x, 0 ≤ f x) →
      (∀ (x : ι → ℝ) (n : ι → ℤ), f (x + fun i => (n i : ℝ)) = f x) → (∃ x, f x ≠ 0) →
      0 < ∫ x in Icc (0 : ι → ℝ) 1, f x := by
  intro ι _ f hf hnn hper ⟨x, hx⟩
  obtain ⟨y, hy⟩ : ∃ y : ι → ℝ, y = fun i => Int.fract (x i) := ⟨_, rfl⟩
  have hxy : x = y + fun i => ((⌊x i⌋ : ℤ) : ℝ) := by
    funext i; subst hy; exact (Int.fract_add_floor (x i)).symm
  have hyne : f y ≠ 0 := by
    have := hper y (fun i => ⌊x i⌋)
    rw [← hxy] at this; rw [← this]; exact hx
  set V : Set (ι → ℝ) := pi univ (fun _ => Ioo (0:ℝ) 1) with hV
  have hVopen : IsOpen V := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have hyV : y ∈ closure V := by
    rw [hV, closure_pi_set]
    intro i _
    rw [closure_Ioo (zero_ne_one)]
    subst hy
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hWopen : IsOpen (Function.support f) := isOpen_ne_fun hf continuous_const
  have hne : (Function.support f ∩ V).Nonempty :=
    mem_closure_iff.mp hyV _ hWopen hyne
  have hpos : 0 < volume (Function.support f ∩ V) := (hWopen.inter hVopen).measure_pos volume hne
  have hVsub : V ⊆ Icc (0 : ι → ℝ) 1 := by
    rw [← pi_univ_Icc]
    exact pi_mono (fun _ _ => Ioo_subset_Icc_self)
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · exact lt_of_lt_of_le hpos (measure_mono (inter_subset_inter_right _ hVsub))
  · exact Filter.Eventually.of_forall (fun z => hnn z)
  · exact hf.continuousOn.integrableOn_compact isCompact_Icc

end GlobalTheory
