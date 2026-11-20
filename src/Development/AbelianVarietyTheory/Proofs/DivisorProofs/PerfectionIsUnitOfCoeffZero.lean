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
import Mathlib.RingTheory.Perfection
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

namespace GlobalTheory

open IsLocalRing

open IsLocalRing in
theorem _root_.GlobalTheory.preTilt_isLocalRing : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Fact ¬IsUnit (p : O)], IsLocalRing (PreTilt O p) := by
  intro p _ O _ _ _
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Perfection.coeff (ModP O p) p 0) := by
    refine ⟨fun x hx => ?_⟩
    have hunit : ∀ n, IsUnit (Perfection.coeff (ModP O p) p n x) := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih =>
        rw [← Perfection.coeff_pow_p' x n] at ih
        exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ih
    let y : Perfection (ModP O p) p := ⟨fun n => ↑(hunit n).unit⁻¹, fun n => by
      have key : (hunit (n + 1)).unit ^ p = (hunit n).unit :=
        Units.ext (by simpa using Perfection.coeff_pow_p' x n)
      rw [← Units.val_pow_eq_pow_val, inv_pow, key]⟩
    have hxy : x * y = 1 := Perfection.ext fun n => by
      rw [map_mul, map_one]
      show Perfection.coeff (ModP O p) p n x * ↑(hunit n).unit⁻¹ = 1
      exact (hunit n).mul_val_inv
    exact ⟨⟨x, y, hxy, mul_comm y x ▸ hxy⟩, rfl⟩
  exact (Perfection.coeff (ModP O p) p 0).domain_isLocalRing

end GlobalTheory
