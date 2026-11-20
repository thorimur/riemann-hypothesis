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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory

namespace GlobalTheory

theorem hermitianForm_norm_sq_le_re_mul_re :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  intro V _ _ Bf hsymm hpos v w
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf y x
      conj_inner_symm := fun x y => by
        show starRingEnd ℂ (Bf x y) = Bf y x
        rw [hsymm x y]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (Bf x x)
        by_cases hx : x = 0
        · subst hx; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show Bf z (x + y) = Bf z x + Bf z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show Bf y (r • x) = starRingEnd ℂ r * Bf y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul] }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c v w
  change ‖Bf w v‖ * ‖Bf v w‖ ≤ RCLike.re (Bf v v) * RCLike.re (Bf w w) at h
  rw [hsymm v w, RCLike.norm_conj] at h
  rw [sq]
  exact h

end GlobalTheory
