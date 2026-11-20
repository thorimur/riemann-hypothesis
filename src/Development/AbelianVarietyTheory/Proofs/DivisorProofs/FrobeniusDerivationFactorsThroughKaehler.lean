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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.FrobDeriv

def FrobTwist (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (M : Type) : Type := M

variable {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime]
  [CharP K p]

instance : AddCommGroup (FrobTwist K p M) := inferInstanceAs (AddCommGroup M)

noncomputable instance : Module K (FrobTwist K p M) :=
  Module.compHom M (frobenius K p)

theorem twist_smul (c : K) (m : FrobTwist K p M) :
    c • m = (c ^ p • (show M from m) : M) := by
  show (frobenius K p c) • (show M from m) = _
  rw [frobenius_def]

end GlobalTheory.DI.FrobDeriv

open GlobalTheory.DI.FrobDeriv in
theorem GlobalTheory.DI.frobDeriv_factors_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  intro K _ M _ _ p _ _ φ hφ
  let ψ : K →ₗ[ℤ] FrobTwist K p M := (φ : K →+ M).toIntLinearMap
  have hone : φ 1 = 0 := by
    have h := hφ 1 1
    simp only [mul_one, one_pow, one_smul] at h
    have : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  let D : Derivation ℤ K (FrobTwist K p M) :=
    { toLinearMap := ψ
      map_one_eq_zero' := hone
      leibniz' := fun a b => by
        show φ (a * b) = a • (show FrobTwist K p M from φ b) + b • (show FrobTwist K p M from φ a)
        rw [twist_smul, twist_smul, hφ]; rfl }
  refine ⟨(D.liftKaehlerDifferential).toAddMonoidHom, ?_, ?_⟩
  · intro c v
    show D.liftKaehlerDifferential (c • v) = _
    rw [LinearMap.map_smul, twist_smul]
    rfl
  · intro a
    show D.liftKaehlerDifferential (KaehlerDifferential.D ℤ K a) = φ a
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl
