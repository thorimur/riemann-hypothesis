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

universe u_1

namespace Bl.general_b_fact_second_variant

theorem goal1 :
  ∀ {k : Type u_1} [inst : Field.{u_1} k] (τ : RingHom.{u_1, u_1} k k),
  (∀ (x : k),
      Eq.{u_1 + 1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} τ (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} τ x)) x) →
    ∀ (θ : k),
      Ne.{u_1 + 1} (HSub.hSub.{u_1, u_1, u_1} θ (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} τ θ)) 0 →
        Eq.{1} (Nat.card.{u_1} k)
          (HPow.hPow.{0, 0, 0}
            (Nat.card.{u_1}
              (Subtype.{u_1 + 1} fun (x : k) ↦ Eq.{u_1 + 1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} τ x) x))
            2)  := by
  intro k _ τ hτ θ hθ
  have hb : ∀ x : k, τ ((x - τ x) / (θ - τ θ)) = (x - τ x) / (θ - τ θ) := by
    intro x
    rw [map_div₀, map_sub, map_sub, hτ, hτ, ← neg_sub x (τ x), ← neg_sub θ (τ θ), neg_div_neg_eq]
  have ha : ∀ x : k, τ (x - (x - τ x) / (θ - τ θ) * θ) = x - (x - τ x) / (θ - τ θ) * θ := by
    intro x
    have e : (x - τ x) / (θ - τ θ) * (θ - τ θ) = x - τ x := div_mul_cancel₀ _ hθ
    rw [map_sub, map_mul, hb x]
    linear_combination e
  let e : k ≃ {x : k // τ x = x} × {x : k // τ x = x} :=
    { toFun := fun x => (⟨x - (x - τ x) / (θ - τ θ) * θ, ha x⟩, ⟨(x - τ x) / (θ - τ θ), hb x⟩)
      invFun := fun p => p.1.1 + p.2.1 * θ
      left_inv := fun x => by
        show x - (x - τ x) / (θ - τ θ) * θ + (x - τ x) / (θ - τ θ) * θ = x
        ring
      right_inv := by
        rintro ⟨⟨a, ha'⟩, ⟨b, hb'⟩⟩
        have h1 : (a + b * θ - τ (a + b * θ)) / (θ - τ θ) = b := by
          rw [map_add, map_mul, ha', hb', div_eq_iff hθ]; ring
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show a + b * θ - (a + b * θ - τ (a + b * θ)) / (θ - τ θ) * θ = a
          rw [h1]; ring
        · show (a + b * θ - τ (a + b * θ)) / (θ - τ θ) = b
          exact h1 }
  rw [Nat.card_congr e, Nat.card_prod, sq]

end Bl.general_b_fact_second_variant
