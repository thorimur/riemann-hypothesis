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
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory.OrderProductDifference

open MvPowerSeries

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (a i))
    (hb : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (b i))
    (hab : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) :
    ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
  classical
  revert ha hb hab
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert j s hj ih =>
    intro ha hb hab
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have key : ∏ i ∈ insert j s, a i - ∏ i ∈ insert j s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by
      rw [Finset.prod_insert hj, Finset.prod_insert hj]; ring
    have hbs : ∑ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, b i) :=
      le_trans (Finset.sum_le_sum fun i hi => hb i (Finset.mem_insert_of_mem hi))
        (MvPowerSeries.le_order_prod _ _)
    rw [key, Finset.sum_insert hj]
    refine le_trans ?_ MvPowerSeries.min_order_le_add
    refine le_min ?_ ?_
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = (k j : ℕ∞) + (∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1) := by rw [add_assoc]
        _ ≤ MvPowerSeries.order (a j) + MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
          add_le_add (ha j (Finset.mem_insert_self _ _)) ih'
        _ ≤ _ := MvPowerSeries.le_order_mul
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = ((k j : ℕ∞) + 1) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) := by rw [add_right_comm]
        _ ≤ MvPowerSeries.order (a j - b j) + MvPowerSeries.order (∏ i ∈ s, b i) :=
          add_le_add (hab j (Finset.mem_insert_self _ _)) hbs
        _ ≤ _ := MvPowerSeries.le_order_mul

theorem target : ∀ {R τ ι : Type} [inst : CommRing R] (s : Finset ι) (a b : ι → MvPowerSeries τ R) (k : ι → ℕ), (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (a i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (b i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) → ∑ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
  fun s a b k ha hb hab => order_prod_sub_prod s a b k ha hb hab

end GlobalTheory.OrderProductDifference
