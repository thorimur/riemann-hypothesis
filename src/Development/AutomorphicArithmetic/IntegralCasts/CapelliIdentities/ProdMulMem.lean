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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace UpperTheory.Reformulated.B.S3

private theorem prod_mul_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (s : Finset (Fin n)) :
    (fun j => (∏ l ∈ s, (d j - d l)) * v j) ∈ W := by
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | insert a s ha ih =>
    have h := W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)
    convert h using 1
    funext j
    simp only [Finset.prod_insert ha, Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
    ring

theorem single_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k) (hd : Function.Injective d)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (i : Fin n) (hi : v i ≠ 0) :
    (Pi.single i 1 : Fin n → k) ∈ W := by
  have h := prod_mul_mem W d hW v hv (Finset.univ.erase i)
  have hc : (∏ l ∈ Finset.univ.erase i, (d i - d l)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun l hl => ?_) hi
    exact sub_ne_zero.mpr fun e => (Finset.ne_of_mem_erase hl) (hd e).symm
  have h2 := W.smul_mem ((∏ l ∈ Finset.univ.erase i, (d i - d l)) * v i)⁻¹ h
  convert h2 using 1
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hc]
  · have hz : (∏ l ∈ Finset.univ.erase i, (d j - d l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (sub_self _)
    rw [Pi.single_eq_of_ne hj, Pi.smul_apply, smul_eq_mul, hz, zero_mul, mul_zero]

end UpperTheory.Reformulated.B.S3
