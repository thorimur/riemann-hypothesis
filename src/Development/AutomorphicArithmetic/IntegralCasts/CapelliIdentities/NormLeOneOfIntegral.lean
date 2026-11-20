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
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.NormLeOneOfIntegral.norm_le_one_of_int :
    ∀ {A K : Type} [inst : CommRing A]
    [inst_1 : NormedField K] [IsUltrametricDist K] [inst_3 : Algebra A K],
    (∀ (a : A), ‖(Algebra.algebraMap A K : A → K) a‖ ≤ (1 : ℝ)) → ∀ {x : K}, IsIntegral A x → ‖x‖ ≤ (1 : ℝ) := by
  intro A K _ _ _ _ h x hx
  let v : Valuation K NNReal := NormedField.valuation
  have hv : ∀ y : K, v y ≤ 1 ↔ ‖y‖ ≤ 1 := fun y => by
    change ‖y‖₊ ≤ 1 ↔ ‖y‖ ≤ 1
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  let f : A →+* v.integer :=
    (algebraMap A K).codRestrict v.integer (fun a => (hv _).2 (h a))
  have hx' : IsIntegral v.integer x :=
    IsIntegral.map_of_comp_eq f (RingHom.id K) (by ext a; rfl) hx
  exact (hv x).1 ((Valuation.integer.integers v).mem_of_integral hx')
