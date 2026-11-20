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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace ReciprocityTheory.ChartRestriction.G.T0

theorem ufd_mem_of_forall_prime {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (x : FractionRing R)
    (h : ∀ p : R, Prime p → ∃ a b : R, ¬ p ∣ b ∧ x * algebraMap R (FractionRing R) b =
      algebraMap R (FractionRing R) a) :
    ∃ a : R, x = algebraMap R (FractionRing R) a := by
  classical
  have key : ∀ c : R, c ≠ 0 → ∀ a0 : R, x * algebraMap R (FractionRing R) c =
      algebraMap R (FractionRing R) a0 → ∃ a : R, x = algebraMap R (FractionRing R) a := by
    intro c
    induction c using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h0; exact absurd rfl h0
    | h₂ u hu =>
      intro _ a0 hx
      refine ⟨a0 * ↑(hu.unit⁻¹), ?_⟩
      have hu' : algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹) = 1 := by
        rw [← map_mul]; simp
      calc x = x * (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹)) := by
              rw [hu', mul_one]
        _ = algebraMap R (FractionRing R) (a0 * ↑(hu.unit⁻¹)) := by rw [← mul_assoc, hx, map_mul]
    | h₃ c p hc hp ih =>
      intro _ a0 hx
      obtain ⟨a, b, hpb, hab⟩ := h p hp
      have hinj := IsFractionRing.injective R (FractionRing R)
      have e1 : a * (p * c) = a0 * b := by
        apply hinj
        simp only [map_mul] at hx hab ⊢
        linear_combination (-(algebraMap R (FractionRing R) p * algebraMap R (FractionRing R) c)) * hab +
          algebraMap R (FractionRing R) b * hx
      have hpa0 : p ∣ a0 := by
        have : p ∣ a0 * b := ⟨a * c, by rw [← e1]; ring⟩
        rcases hp.dvd_or_dvd this with h1 | h1
        · exact h1
        · exact absurd h1 hpb
      obtain ⟨a1, rfl⟩ := hpa0
      have hp0 : algebraMap R (FractionRing R) p ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
        exact fun h' => hp.ne_zero (hinj h')
      refine ih hc a1 ?_
      apply mul_left_cancel₀ hp0
      simp only [map_mul] at hx ⊢
      linear_combination hx
  obtain ⟨a0, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine key c hc0 a0 ?_
  rw [div_mul_cancel₀]
  rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
  exact fun h' => hc0 (IsFractionRing.injective R (FractionRing R) h')

end ReciprocityTheory.ChartRestriction.G.T0
