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
import Mathlib.LinearAlgebra.Eigenspace.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Module Module.End

namespace Bl.general_b_fact_left_last

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private lemma pz {T : End K V} {x : V} {k m : ℕ} (hkm : k ≤ m) (hx : (T ^ k) x = 0) :
    (T ^ m) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [show k + d = d + k from Nat.add_comm k d, pow_add, Module.End.mul_apply, hx, map_zero]

theorem goal1 {A B : End K V} (h : Commute A B) {a b : K} {x : V}
    (hA : x ∈ A.maxGenEigenspace a) (hB : x ∈ B.maxGenEigenspace b) :
    x ∈ (A * B).maxGenEigenspace (a * b) := by
  rw [mem_maxGenEigenspace] at hA hB ⊢
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  have hNB : Commute (A - a • 1) B := h.sub_left ((Commute.one_left B).smul_left a)
  have hNM : Commute (A - a • 1) (B - b • 1) :=
    hNB.sub_right ((Commute.one_right _).smul_right b)
  have hBM : Commute B (B - b • 1) :=
    (Commute.refl B).sub_right ((Commute.one_right B).smul_right b)
  have key : A * B - (a * b) • (1 : End K V) = (A - a • 1) * B + a • (B - b • 1) := by
    rw [sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]; abel
  have hc : Commute ((A - a • 1) * B) (a • (B - b • 1)) := (hNM.mul_left hBM).smul_right a
  refine ⟨k + l, ?_⟩
  rw [key, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, hNB.mul_pow, smul_pow]
  refine (congrArg _ ?_).trans (smul_zero _)
  rcases le_or_gt k m with hkm | hkm
  · have hC : Commute ((A - a • 1) ^ m) (B ^ m * (a ^ (k + l - m) • (B - b • 1) ^ (k + l - m))) :=
      (hNB.pow_pow m m).mul_right ((hNM.pow_pow m (k + l - m)).smul_right _)
    rw [mul_assoc, hC.eq, Module.End.mul_apply, pz hkm hk, map_zero]
  · rw [Module.End.mul_apply, LinearMap.smul_apply, pz (by omega) hl, smul_zero, map_zero]

end Bl.general_b_fact_left_last
