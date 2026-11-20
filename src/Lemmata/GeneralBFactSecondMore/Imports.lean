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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

namespace Bl.general_b_fact_second'

theorem goal1 :
  ∀ {E U : Type} [inst : Field.{0} E] [NumberField.{0} E] [inst_2 : AddCommGroup.{0} U] [inst_3 : Module.{0, 0} E U]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) U]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E U]
  (N : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) U),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} N)) Top.top.{0} →
    ∀ (x : U),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} N (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro E U _ _ _ _ _ _ N hN x
  have hx : x ∈ Submodule.span E (N : Set U) := by rw [hN]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    apply N.add_mem
    · rw [mul_comm, mul_smul]; exact N.smul_mem d2 h1
    · rw [mul_smul]; exact N.smul_mem d1 h2
  | smul a y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨n, m⟩, hm⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    have key : ((m : NumberField.RingOfIntegers E)) • (a • y) = n • y := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm]
      simp only at hm
      rw [hm, algebraMap_smul]
    refine ⟨d * m, mul_ne_zero hd (nonZeroDivisors.coe_ne_zero m), ?_⟩
    rw [mul_smul, key, ← mul_smul, mul_comm, mul_smul]
    exact N.smul_mem n h

end Bl.general_b_fact_second'
