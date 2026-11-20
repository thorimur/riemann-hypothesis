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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open Module

namespace GlobalTheory

theorem exists_invertible_matrix_rows_span : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (Y₀ : Submodule F (κ → F)),
    ∃ P : Matrix κ κ F, IsUnit P.det ∧ ∃ s : Set κ, (∀ i ∈ s, P i ∈ Y₀) ∧
      ∀ y ∈ Y₀, ∃ c : κ → F, (∀ i ∉ s, c i = 0) ∧ y = Matrix.vecMul c P := by
  intro F _ κ _ _ Y₀
  obtain ⟨S, hSY, hspan, hli⟩ := exists_linearIndependent F (Y₀ : Set (κ → F))
  have hli' : LinearIndepOn F id S := hli
  let B := Basis.extend hli'
  let e := B.indexEquiv (Pi.basisFun F κ)
  let v : κ → (κ → F) := fun i => ((e.symm i : _) : κ → F)
  have hv : ∀ i, v i = B.reindex e i := by
    intro i; simp [v, B, Basis.reindex_apply, Basis.coe_extend]
  refine ⟨Matrix.of v, ?_, {i | v i ∈ S}, ?_, ?_⟩
  · apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    have : v = ⇑(B.reindex e) := funext hv
    have h2 : LinearIndependent F v := by
      rw [this]; exact (B.reindex e).linearIndependent
    exact h2
  · intro i hi; exact hSY hi
  · intro y hy
    have himg : v '' {i | v i ∈ S} = S := by
      ext x; simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hx
        refine ⟨e ⟨x, hli'.subset_extend (Set.subset_univ _) hx⟩, ?_, ?_⟩ <;> simp [v, hx]
    have hy' : y ∈ Submodule.span F (v '' {i | v i ∈ S}) := by
      rw [himg, hspan, Submodule.span_eq]; exact hy
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination F).mp hy'
    refine ⟨l, fun i hi => ?_, ?_⟩
    · by_contra h
      exact hi ((Finsupp.mem_supported _ _).mp hl (Finsupp.mem_support_iff.mpr h))
    · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

end GlobalTheory
