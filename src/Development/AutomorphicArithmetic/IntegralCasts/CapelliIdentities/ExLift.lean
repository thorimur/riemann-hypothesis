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

theorem UpperTheory.Reformulated.B.Qj6.ex_lift :
    ∀ {M Ω C : Type} [inst : Field M] [NumberField M] [inst_2 : Field Ω]
    [CharZero Ω] [IsAlgClosed Ω] [inst_5 : Field C] [CharZero C] (j : Ω →+* C) (f : M →+* C),
    ∃ (g : M →+* Ω), ∀ (x : M), (j : Ω → C) ((g : M → Ω) x) = (f : M → C) x := by
  intro M Ω C _ _ _ _ _ _ _ j f
  have key : ∀ x : M, f x ∈ j.fieldRange := by
    intro x
    have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hs : ((minpoly ℚ x).map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
    have hm : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j = (minpoly ℚ x).map (algebraMap ℚ C) := by
      rw [Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hne : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j ≠ 0 := by
      rw [hm]
      exact ((minpoly.monic hx).map _).ne_zero
    have hr : f x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne, hm, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      have h := Polynomial.aeval_algHom_apply f.toRatAlgHom x (minpoly ℚ x)
      rw [minpoly.aeval, map_zero] at h
      exact h
    rw [hs.roots_map, Multiset.mem_map] at hr
    obtain ⟨y, -, hy⟩ := hr
    exact ⟨y, hy⟩
  choose g hg using fun x => RingHom.mem_fieldRange.mp (key x)
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hg⟩
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
