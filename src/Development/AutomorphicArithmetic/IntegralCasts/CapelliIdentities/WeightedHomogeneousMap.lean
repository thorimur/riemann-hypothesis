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

theorem UpperTheory.aeval_map_eq_rename_map_iff :
    ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S), Function.Injective φ → ∀ (σ M : Type) [AddCommMonoid M] (w : σ → M) (ν : M) (f : MvPolynomial σ R), (MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.map φ f) ν ↔ MvPolynomial.IsWeightedHomogeneous w f ν) ∧ ∀ (τ : Type) (gR : σ → MvPolynomial τ R) (gS : σ → MvPolynomial τ S) (ρ : σ → τ), (∀ v, MvPolynomial.map φ (gR v) = gS v) → (MvPolynomial.aeval gS (MvPolynomial.map φ f) = MvPolynomial.rename ρ (MvPolynomial.map φ f) ↔ MvPolynomial.aeval gR f = MvPolynomial.rename ρ f) := by
  intro R S _ _ φ hφ σ M _ w ν f
  refine ⟨?_, ?_⟩
  · unfold MvPolynomial.IsWeightedHomogeneous
    refine forall_congr' fun d => ?_
    rw [MvPolynomial.coeff_map, map_ne_zero_iff φ hφ]
  · intro τ gR gS ρ hg
    have hgS : gS = fun v => MvPolynomial.map φ (gR v) := funext fun v => (hg v).symm
    subst hgS
    rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.map_bind₁,
      ← MvPolynomial.map_rename]
    exact (MvPolynomial.map_injective φ hφ).eq_iff
