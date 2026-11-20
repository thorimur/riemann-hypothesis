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
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.RingHom
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

namespace GlobalTheory.ChF

private theorem nonempty_padicInt_ringHom (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (I : Ideal O) [IsAdicComplete I O] (hp : (p : O) ∈ I) : Nonempty (ℤ_[p] →+* O) := by
  have hd : ∀ n : ℕ, ringChar (O ⧸ I ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk (I ^ n)), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow hp n
  refine ⟨IsAdicComplete.liftRingHom I
    (fun n => (ZMod.castHom (hd n) (O ⧸ I ^ n)).comp (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact RingHom.ext_zmod _ _

private theorem padicInt_ringHom_matrix_ext (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (n : ℕ)
    (f g : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]) : f c = g c := by
  ext i j
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(p : O)}) inferInstance _ fun k => ?_
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k c)
  have hc : c = (c.appr k : ℤ_[p]) + ((p ^ k : ℕ) : ℤ_[p]) * d := by
    rw [Nat.cast_pow, ← hd]; ring
  have h : f c - g c = (p ^ k : ℕ) • (f d - g d) := by
    rw [hc]
    simp only [map_add, map_mul, map_natCast, nsmul_eq_mul, mul_sub]
    abel
  have h' : f c i j - g c i j = (p : O) ^ k * (f d i j - g d i j) := by
    have := congrFun (congrFun h i) j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sub_apply, nsmul_eq_mul, Nat.cast_pow] at this
    exact this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem padicInt_algebra_of_isAdicComplete_and_matrix_unique :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O],
      Nonempty (Algebra ℤ_[p] O) ∧ ∀ [Algebra ℤ_[p] O] (n : ℕ)
        (f : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]),
        f c = algebraMap ℤ_[p] O c • (1 : Matrix (Fin n) (Fin n) O) := by
  intro p _ O _ _
  refine ⟨?_, fun n f c => ?_⟩
  · obtain ⟨φ⟩ := nonempty_padicInt_ringHom p O _ (Ideal.mem_span_singleton_self _)
    exact ⟨φ.toAlgebra⟩
  · rw [padicInt_ringHom_matrix_ext p O n f
      ((algebraMap O (Matrix (Fin n) (Fin n) O)).comp (algebraMap ℤ_[p] O)) c,
      RingHom.comp_apply, Algebra.algebraMap_eq_smul_one (A := Matrix (Fin n) (Fin n) O)]

end GlobalTheory.ChF
