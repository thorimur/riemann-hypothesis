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
import Mathlib.LinearAlgebra.Eigenspace.Basic
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
import Mathlib.Topology.Sheaves.Presheaf

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem finiteDimensional_ker_aeval_of_eigenspaces
    (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (hT : ∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) (p : Polynomial ℂ) (hp : p ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  by_cases h0 : p.degree = 0
  · have hu : IsUnit p := Polynomial.isUnit_iff_degree_eq_zero.mpr h0
    have hu' : IsUnit (Polynomial.aeval T p) := hu.map _
    have hk : LinearMap.ker (Polynomial.aeval T p) = ⊥ :=
      LinearMap.ker_eq_bot.mpr ((Module.End.isUnit_iff _).mp hu').1
    rw [hk]
    infer_instance
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p h0
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr ha
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
      exact hp hq
    have hdeg : q.natDegree < n := by
      rw [← hn, hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0,
        Polynomial.natDegree_X_sub_C]
      omega
    have ihq := ih _ hdeg q hq0 rfl
    have hfg : (LinearMap.ker (Polynomial.aeval T p)).FG := by
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (Polynomial.aeval T q)
      · have hle : (LinearMap.ker (Polynomial.aeval T p)).map (Polynomial.aeval T q)
            ≤ T.eigenspace a := by
          rintro _ ⟨x, hx, rfl⟩
          rw [Module.End.mem_eigenspace_iff]
          have hx' : Polynomial.aeval T p x = 0 := hx
          rw [hq, map_mul, Module.End.mul_apply] at hx'
          simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
            Module.algebraMap_end_apply] at hx'
          exact sub_eq_zero.mp hx'
        haveI := hT a
        exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le hle)
      · exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le
          (inf_le_right : _ ≤ LinearMap.ker (Polynomial.aeval T q)))
    exact (Module.Finite.iff_fg).mpr hfg

end GlobalTheory
