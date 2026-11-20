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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_eq_smul_of_forall_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) →
      ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  intro O M _ _ _ a ha l hl
  have cancel : ∀ x y : O, a * x = a * y → x = y := by
    intro x y hxy
    have := ha (x - y) (by rw [mul_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  let c : M → O := fun w => Classical.choose (hl w)
  have hc : ∀ w, l w = a * c w := fun w => Classical.choose_spec (hl w)
  refine ⟨{ toFun := c, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply cancel
    rw [mul_add, ← hc, ← hc, ← hc, map_add]
  · intro r x
    apply cancel
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hc, map_smul, hc, smul_eq_mul]
    ring
  · ext w
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    exact hc w

end GlobalTheory
