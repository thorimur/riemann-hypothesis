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
import Mathlib.Topology.Sheaves.Init

open MeasureTheory

theorem UpperTheory.ConvolutionTheory.K.intEst :
    ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (h : X → ℝ) (k c o : X → ℂ) (Z A B : ℝ),
      Measurable h → Integrable c ν → AEStronglyMeasurable o ν → 0 ≤ A → 0 ≤ B → (∀ x, k x = c x + o x) → (∀ x, Z < h x → k x = 0) →
      (∀ x, h x ≤ Z → ‖o x‖ ≤ A) → (∀ x, Z < h x → ‖c x‖ ≤ B) →
      ‖∫ x, k x ∂ν - ∫ x, c x ∂ν‖ ≤ ν.real Set.univ * A + ν.real Set.univ * B := by
  intro X _ ν _ h k c o Z A B hh hc ho hA hB hk h0 hoA hcB
  set S : Set X := {x | h x ≤ Z}
  have hS : MeasurableSet S := measurableSet_le hh measurable_const
  have e1 : ∀ x, k x - c x = S.indicator o x - Sᶜ.indicator c x := by
    intro x
    by_cases hx : x ∈ S
    · simp [hx, hk x]
    · simp [hx, h0 x (not_le.1 hx)]
  have b1 : ∀ x, ‖S.indicator o x‖ ≤ A := fun x => by
    by_cases hx : x ∈ S
    · simpa [hx] using hoA x hx
    · simpa [hx] using hA
  have b2 : ∀ x, ‖Sᶜ.indicator c x‖ ≤ B := fun x => by
    by_cases hx : x ∈ S
    · simpa [hx] using hB
    · simpa [hx] using hcB x (not_le.1 hx)
  have i1 : Integrable (S.indicator o) ν := Integrable.of_bound (ho.indicator hS) A (Filter.Eventually.of_forall b1)
  have i2 : Integrable (Sᶜ.indicator c) ν := hc.indicator hS.compl
  have ik : Integrable k ν := by
    have : k = fun x => (S.indicator o x - Sᶜ.indicator c x) + c x := funext fun x => by rw [← e1]; ring
    rw [this]
    exact (i1.sub i2).add hc
  rw [← integral_sub ik hc]
  simp_rw [e1]
  rw [integral_sub i1 i2]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [mul_comm]; exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall b1)
  · rw [mul_comm]; exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall b2)
