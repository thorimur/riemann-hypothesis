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

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe40.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qe40.IsUp :
    {R : Type} → [CommRing R] → UpperTheory.Reformulated.B.Qe40.M4 R → Prop :=
    fun {R : Type} [CommRing R] (X : UpperTheory.Reformulated.B.Qe40.M4 R) ↦ ∀ (i j : Fin (4 : ℕ)), j < i → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qe40.up_diag_mul :
    ∀ {R : Type} [inst : CommRing R] {X Y : UpperTheory.Reformulated.B.Qe40.M4 R},
      UpperTheory.Reformulated.B.Qe40.IsUp X → UpperTheory.Reformulated.B.Qe40.IsUp Y → ∀ (i : Fin (4 : ℕ)), (X * Y) i i = X i i * Y i i := by
  intro R _ X Y hX hY i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]
