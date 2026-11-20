import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace PositivityTheory.Lord

theorem hasProd_compl_finset {ι : Type*} [DecidableEq ι] (f g : ι → ℂ) (a : ℂ) (T S : Finset ι) (hST : S ⊆ T)
    (hg : HasProd g a) (hg0 : ∀ v ∈ T, g v ≠ 0) (hfg : ∀ v, v ∉ T → f v = g v) :
    HasProd (fun v : {v // v ∉ S} => f v) (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by
  let F : ι → ℂ := Set.mulIndicator {v | v ∉ S} f
  let k : ι → ℂ := fun v => if v ∈ T then (g v)⁻¹ * F v else 1
  have hkT : HasProd k (∏ v ∈ T, k v) :=
    hasProd_prod_of_ne_finset_one (fun v hv => if_neg hv)
  have hgk : ∀ v, g v * k v = F v := by
    intro v
    by_cases hv : v ∈ T
    · show g v * (if v ∈ T then (g v)⁻¹ * F v else 1) = F v
      rw [if_pos hv, ← mul_assoc, mul_inv_cancel₀ (hg0 v hv), one_mul]
    · have hvS : v ∉ S := fun h => hv (hST h)
      show g v * (if v ∈ T then (g v)⁻¹ * F v else 1) = Set.mulIndicator {v | v ∉ S} f v
      rw [if_neg hv, mul_one, Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hvS), hfg v hv]
  have hFT : ∏ v ∈ T, F v = ∏ v ∈ T \ S, f v := by
    rw [Finset.sdiff_eq_filter, Finset.prod_filter]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    by_cases hvS : v ∈ S
    · rw [if_neg (not_not.2 hvS)]
      exact Set.mulIndicator_of_notMem (show v ∉ {v | v ∉ S} from not_not.2 hvS) f
    · rw [if_pos hvS]
      exact Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hvS) f
  have hkprod : ∏ v ∈ T, k v = (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v := by
    rw [← hFT, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v hv => if_pos hv)
  have hF : HasProd F (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by
    have h := hg.mul hkT
    rw [hkprod, ← mul_assoc] at h
    convert h using 1
    funext v
    exact (hgk v).symm
  exact (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 hF

end PositivityTheory.Lord
