import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.kb :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ AlgebraicClosure (ZMod p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.WW :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ WittVector p (UpperTheory.Reformulated.B.Qi32.kb p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.K0 :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ FractionRing (UpperTheory.Reformulated.B.Qi32.WW p)

theorem UpperTheory.Reformulated.B.Qi32.mem_W_of_norm :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (i0 : UpperTheory.Reformulated.B.Qi32.K0 p →+* ℂ_[p]),
      (∀ (x : UpperTheory.Reformulated.B.Qi32.WW p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p])
                ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  x)‖ ≤
            (1 : ℝ)) →
        ∀ (x : UpperTheory.Reformulated.B.Qi32.K0 p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p]) x‖ ≤ (1 : ℝ) →
            ∃ (w : UpperTheory.Reformulated.B.Qi32.WW p),
              (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  w =
                x := by
  intro p inst i0 hW x hx
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
    rw [h, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rcases ValuationRing.isInteger_or_isInteger (UpperTheory.Reformulated.B.Qi32.WW p) x with h | ⟨w, hw⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, map_zero _⟩
  by_cases hu : IsUnit w
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : (UpperTheory.Reformulated.B.Qi32.WW p)ˣ) : UpperTheory.Reformulated.B.Qi32.WW p), ?_⟩
    rw [map_units_inv, hw, inv_inv]
  · exfalso
    have hirr : Irreducible (p : UpperTheory.Reformulated.B.Qi32.WW p) := WittVector.irreducible p
    have hmem : w ∈ IsLocalRing.maximalIdeal (UpperTheory.Reformulated.B.Qi32.WW p) := hu
    rw [hirr.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨v, rfl⟩ := hmem
    have h1 : ‖i0 x‖ * ‖i0 x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
    have h2 : ‖i0 x⁻¹‖ < 1 := by
      rw [← hw, map_mul, map_mul, map_natCast, map_natCast, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hW v)) hp
    have h3 : ‖i0 x‖ * ‖i0 x⁻¹‖ ≤ ‖i0 x⁻¹‖ := mul_le_of_le_one_left (norm_nonneg _) hx
    linarith
