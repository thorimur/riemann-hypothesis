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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

noncomputable def UpperTheory.Reformulated.B.ComplementSubspace.IsCompl :
    {K : Type} → [Field K] → {n r : ℕ} → Matrix (Fin r) (Fin n) K → Matrix (Fin n) (Fin n) K → Prop :=
    fun {K : Type} [Field K] {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (a : Matrix (Fin n) (Fin n) K) ↦
      IsUnit a.det ∧ ∀ (i : Fin n) (hi : (↑i : ℕ) < r), a i = c (⟨(↑i : ℕ), hi⟩ : Fin r)

namespace ComplementBasis

private lemma basis_sub {K : Type} [Field K] {n : ℕ} (U : Submodule K (Fin n → K)) :
    ∃ c : Fin (Module.finrank K U) → (Fin n → K),
      LinearIndependent K c ∧ Submodule.span K (Set.range c) = U := by
  let b := Module.finBasis K U
  refine ⟨fun i => (b i : Fin n → K), ?_, ?_⟩
  · exact b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have : Set.range (fun i => (b i : Fin n → K)) = U.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

end ComplementBasis

open ComplementBasis in
theorem UpperTheory.Reformulated.B.ComplementSubspace.main :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (U : Submodule K (Fin n → K)),
      ∃ (c : Matrix (Fin (Module.finrank K ↥U)) (Fin n) K) (a : Matrix (Fin n) (Fin n) K),
        (LinearIndependent K c ∧ Submodule.span K (Set.range c) = U) ∧ UpperTheory.Reformulated.B.ComplementSubspace.IsCompl c a := by
  intro K _ n U
  obtain ⟨c, hcli, hcsp⟩ := basis_sub U
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  obtain ⟨w, hwli, hwsp⟩ := basis_sub W
  have hrm : Module.finrank K U + Module.finrank K W = n := by
    have := Submodule.finrank_add_eq_of_isCompl hUW
    rw [Module.finrank_fin_fun] at this
    omega
  let a : Matrix (Fin n) (Fin n) K := fun i =>
    if h : (i : ℕ) < Module.finrank K U then c ⟨i, h⟩ else w ⟨(i : ℕ) - Module.finrank K U, by have := i.2; omega⟩
  refine ⟨c, a, ⟨hcli, hcsp⟩, ?_, ?_⟩
  · let e : Fin (Module.finrank K U) ⊕ Fin (Module.finrank K W) ≃ Fin n := finSumFinEquiv.trans (finCongr hrm)
    have hg : LinearIndependent K (Sum.elim c w) := by
      apply LinearIndependent.sum_type hcli hwli
      rw [hcsp, hwsp]; exact hUW.disjoint
    have hae : (fun i => a i) ∘ e = Sum.elim c w := by
      funext x
      rcases x with j | k
      · simp [e, a]
      · simp [e, a]
    have hla : LinearIndependent K (fun i => a i) := by
      rw [← linearIndependent_equiv e, hae]; exact hg
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.linearIndependent_rows_iff_isUnit.mp hla
  · intro i hi
    simp [a, hi]
