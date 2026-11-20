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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Presheaf

namespace UpperTheory.Reformulated.B.NormLeOneOfIsIntegral

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hle : ∀ y : PadicAlgCl l,
      y ∈ (PadicAlgCl.valued l).v.integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hmem : ∀ a : ℤ_[l],
      algebraMap ℤ_[l] (PadicAlgCl l) a ∈ (PadicAlgCl.valued l).v.integer := by
    intro a
    rw [hle, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (PadicAlgCl.norm_extends l _).trans_le a.2
  have hint : IsIntegral (PadicAlgCl.valued l).v.integer x :=
    hx.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict _ hmem) (RingHom.id _) rfl
  exact (hle x).1 ((Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral hint)

end UpperTheory.Reformulated.B.NormLeOneOfIsIntegral
