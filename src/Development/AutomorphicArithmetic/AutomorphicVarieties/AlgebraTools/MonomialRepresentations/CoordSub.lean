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

open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.coordSub :
    ∀ (C ι : Type) [CommRing C] [Fintype ι] [DecidableEq ι] (d : ι → C), (∀ i j, i ≠ j → IsUnit (d i - d j)) →
      ∀ W : Submodule C (ι → C), (∀ w ∈ W, diagonal d *ᵥ w ∈ W) → ∀ w ∈ W, ∀ i, Pi.single i (w i) ∈ W := by
  intro C ι _ _ _ d hd W hD w hw i
  have key : ∀ S : Finset ι, (fun k => (∏ j ∈ S, (d k - d j)) * w k) ∈ W := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simpa using hw
    · intro j S hj ih
      have h2 := W.sub_mem (hD _ ih) (W.smul_mem (d j) ih)
      convert h2 using 1
      funext k
      simp only [Finset.prod_insert hj, mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (d i - d j)) :=
    IsUnit.prod_iff.mpr fun j hj => hd i j (Finset.ne_of_mem_erase hj).symm
  have h3 := W.smul_mem (↑hu.unit⁻¹ : C) (key (Finset.univ.erase i))
  convert h3 using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · have hz : ∏ j ∈ Finset.univ.erase i, (d k - d j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp [Pi.single_eq_of_ne hk, hz]
