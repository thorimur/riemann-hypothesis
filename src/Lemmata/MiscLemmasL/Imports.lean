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

open Module

namespace Bl.SecondBlockLemmaM

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem goal1 [IsDomain R] [IsFractionRing R C]
    {V : Type} [AddCommGroup V] [Module C V] [Module R V] [IsScalarTower R C V]
    (S : Submodule R V) {x : V} (hx : x ∈ Submodule.span C (S : Set V)) :
    ∃ r : R, r ≠ 0 ∧ r • x ∈ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hrs⟩ := hy
    obtain ⟨s, hs, hss⟩ := hz
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    have h : (r * s) • (y + z) = s • (r • y) + r • (s • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm s r]
    rw [h]
    exact S.add_mem (S.smul_mem s hrs) (S.smul_mem r hss)
  | smul c y _ hy =>
    obtain ⟨r, hr, hrs⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) c
    have hab' : c * algebraMap R C (b : R) = algebraMap R C a := hab
    refine ⟨(b : R) * r, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hr, ?_⟩
    have h : ((b : R) * r) • (c • y) = a • (r • y) := by
      calc ((b : R) * r) • (c • y) = r • ((b : R) • (c • y)) := by rw [mul_comm, mul_smul]
        _ = r • (((b : R) • c) • y) := by rw [smul_assoc]
        _ = r • ((algebraMap R C a) • y) := by rw [Algebra.smul_def, mul_comm, hab']
        _ = r • (a • y) := by rw [algebraMap_smul]
        _ = a • (r • y) := smul_comm r a y
    rw [h]
    exact S.smul_mem a hrs

end Bl.SecondBlockLemmaM
