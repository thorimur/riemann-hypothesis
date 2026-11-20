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

theorem UpperTheory.Reformulated.B.SingleMemOfDiagonal.single_mem_of_diag :
    ∀ {κ : Type} [inst : Field κ] {m : ℕ} (d : Fin m → κ),
    Function.Injective d →
      ∀ (W : Submodule κ (Fin m → κ)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ v ∈ W, ∀ (i : Fin m), v i ≠ (0 : κ) → Pi.single i (1 : κ) ∈ W := by
  intro κ _ m d hd W hW v hv i hi
  have key : ∀ s : Finset (Fin m), (fun k => (∏ j ∈ s, (d k - d j)) * v k) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hv
    | insert a s ha ih =>
      have h := W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)
      convert h using 1
      funext k
      simp only [Finset.prod_insert ha, Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply,
        smul_eq_mul]
      ring
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => ?_) hi
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (key (Finset.univ.erase i))
  convert h using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    exact (inv_mul_cancel₀ hc).symm
  · have h0 : (∏ j ∈ Finset.univ.erase i, (d k - d j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp only [Pi.single_eq_of_ne hk, Pi.smul_apply, smul_eq_mul, h0, zero_mul, mul_zero]
