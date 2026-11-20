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

namespace ZbYhc5Helpers

private lemma key {g : ℕ} (c : ℂ) (u u' : Fin g → ℂ) :
    c • (u + Complex.I • u') = (c.re • u - c.im • u') + Complex.I • (c.im • u + c.re • u') := by
  funext i
  apply Complex.ext <;> simp [Complex.real_smul] <;> ring

end ZbYhc5Helpers

theorem UpperTheory.Reformulated.B.Yhc5.main :
    ∀ {g : ℕ} {T : Set (Fin g → ℂ)} {w : Fin g → ℂ},
      w ∈ Submodule.span ℂ T → ∃ u ∈ Submodule.span ℝ T, ∃ u' ∈ Submodule.span ℝ T, w = u + Complex.I • u' := by
  intro g T w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨x, Submodule.subset_span hx, 0, Submodule.zero_mem _, by simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    obtain ⟨b, hb, b', hb', rfl⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', by
      rw [smul_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    refine ⟨c.re • a - c.im • a', ?_, c.im • a + c.re • a', ?_, ZbYhc5Helpers.key c a a'⟩
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
