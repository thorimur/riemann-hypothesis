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
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.MultiDimensional.multi_dim :
    ∀ {P : Type} [inst : Fintype P] (g : P → ℤ → ENNReal), ∑' (x : P → ℤ), ∏ p : P, g p (x p) ≤ ∏ p : P, ∑' (n : ℤ), g p n := by
  intro P _ g
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ x ∈ s, ∏ p : P, g p (x p)
      ≤ ∑ x ∈ Fintype.piFinset (fun p => s.image (fun y : P → ℤ => y p)), ∏ p : P, g p (x p) := by
        refine Finset.sum_le_sum_of_subset fun x hx => ?_
        exact Fintype.mem_piFinset.2 fun p => Finset.mem_image_of_mem _ hx
    _ = ∏ p : P, ∑ n ∈ s.image (fun y : P → ℤ => y p), g p n :=
        (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ p : P, ∑' (n : ℤ), g p n :=
        Finset.prod_le_prod' fun p _ => ENNReal.sum_le_tsum _
