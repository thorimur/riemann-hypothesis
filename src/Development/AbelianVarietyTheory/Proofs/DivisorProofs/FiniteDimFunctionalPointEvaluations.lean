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
import Mathlib.RingTheory.PicardGroup
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

open Module

namespace GlobalTheory

theorem exists_eval_combination (Xt : Type) (S : Submodule ℂ (Xt → ℂ)) [FiniteDimensional ℂ S]
    (l : S →ₗ[ℂ] ℂ) :
    ∃ (n : ℕ) (x : Fin n → Xt) (c : Fin n → ℂ), ∀ f : S, l f = ∑ i, c i * (f : Xt → ℂ) (x i) := by
  let E : Xt → Dual ℂ S := fun x => (LinearMap.proj x : (Xt → ℂ) →ₗ[ℂ] ℂ).comp S.subtype
  have hE : ∀ x (f : S), E x f = (f : Xt → ℂ) x := fun _ _ => rfl
  set W : Submodule ℂ (Dual ℂ S) := Submodule.span ℂ (Set.range E) with hWdef
  have hco : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_dualCoannihilator] at hf
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    have := hf (E x) (Submodule.subset_span ⟨x, rfl⟩)
    simpa [hE] using this
  have hW : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hco]
    exact Submodule.dualAnnihilator_bot
  have hl : l ∈ W := by rw [hW]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp hl
  choose x hx using fun i => (g i).2
  refine ⟨n, x, c, fun f => ?_⟩
  rw [← hg]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i, hE]

end GlobalTheory
