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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace Bl.general_b_fact_second''

theorem goal1 :
  ∀ {O K X : Type} [inst : CommRing.{0} O] [IsDomain.{0} O] [inst_2 : Field.{0} K] [inst_3 : Algebra.{0, 0} O K]
  [IsFractionRing.{0, 0} O K] [inst_5 : AddCommGroup.{0} X] [inst_6 : Module.{0, 0} K X] [inst_7 : Module.{0, 0} O X]
  [IsScalarTower.{0, 0, 0} O K X] (B : Submodule.{0, 0} O X),
  Eq.{1} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} B)) Top.top.{0} →
    ∀ (x : X), Exists.{1} fun (d : O) ↦ And (Ne.{1} d 0) (Membership.mem.{0, 0} B (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro O K X _ _ _ _ _ _ _ _ _ B hB x
  have hx : x ∈ Submodule.span K (B : Set X) := by rw [hB]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact B.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d2 * d1, mul_ne_zero hd2 hd1, ?_⟩
    rw [smul_add]
    apply B.add_mem
    · rw [mul_smul]; exact B.smul_mem d2 h1
    · rw [mul_comm, mul_smul]; exact B.smul_mem d1 h2
  | smul k y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) k
    have hb0 : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hk : algebraMap O K b * (algebraMap O K a / algebraMap O K b) = algebraMap O K a := by
      field_simp
    have key : b • ((algebraMap O K a / algebraMap O K b) • y) = a • y := by
      rw [← smul_assoc, Algebra.smul_def, hk, algebraMap_smul]
    refine ⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero hb), ?_⟩
    rw [mul_smul, key, smul_comm]
    exact B.smul_mem a h

end Bl.general_b_fact_second''
