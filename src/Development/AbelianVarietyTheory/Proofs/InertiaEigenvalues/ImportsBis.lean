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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
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

namespace GlobalTheory.IntegralCriterion

theorem main : ∀ (k : Type) [inst : Field k] (n : ℕ) (v : Fin (n + (1 : ℕ)) → k), v ≠ (0 : Fin (n + (1 : ℕ)) → k) → ∃ (P : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k), IsUnit P ∧ ∀ (a : Fin (n + (1 : ℕ))), P a (0 : Fin (n + (1 : ℕ))) = v a := by
  intro k _ n v hv
  set e0 : Fin (n + 1) → k := Pi.single 0 1 with he0def
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  let f : (k ∙ e0) ≃ₗ[k] (k ∙ v) :=
    (LinearEquiv.toSpanNonzeroSingleton k _ e0 he0).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton k _ v hv
  have hf : (f ⟨e0, Submodule.mem_span_singleton_self e0⟩ : Fin (n + 1) → k) = v := by
    have h1 : (⟨e0, Submodule.mem_span_singleton_self e0⟩ : k ∙ e0) =
        LinearEquiv.toSpanNonzeroSingleton k _ e0 he0 1 := by
      ext; simp
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
    simp
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hge : g e0 = v := by
    rw [← hf, hg]
  refine ⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩
  · refine ⟨⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)),
      LinearMap.toMatrix' (g.symm : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩, rfl⟩
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
  · intro a
    rw [LinearMap.toMatrix'_apply]
    change g e0 a = v a
    rw [hge]

end GlobalTheory.IntegralCriterion
