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
import Mathlib.NumberTheory.Padics.PadicIntegers
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

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

def tauX {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE] {R : Type} [CommRing R] [Algebra ℤ_[l] R] (τ : OE →+* R) :
    (ℤ_[l] ⊗[ℤ] OE) →ₐ[ℤ_[l]] R :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[l] R) τ.toIntAlgHom (fun _ _ => Commute.all _ _)

def EmbX {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE] {R : Type} [CommRing R] [Algebra ℤ_[l] R]
    (e : ℤ_[l] ⊗[ℤ] OE) : Set (OE →+* R) := {τ | tauX τ e = 1}

def PlaceX (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ e : ℤ_[l] ⊗[ℤ] OE, e * e = e ∧ e ≠ 0 ∧ (∀ f : ℤ_[l] ⊗[ℤ] OE, f * f = f → f * e = f → f = 0 ∨ f = e) ∧
    ∃ (_ : NeZero (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))))
      (t : Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) ≃ EmbX (R := R) e)
      (jj : ZMod d ≃ Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))),
      (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))) ℤ_[l]
          (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)),
        IsUnit (Matrix.det (Matrix.of fun i j =>
          tauX ((t j : EmbX (R := R) e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def PlaceXSt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra ℤ_[l] R],
    (l : R) ∈ maximalIdeal R → ¬ ((l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (d : ℕ) [NeZero d] (em : ZMod d → OE →+* R),
      (∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) →
      (∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) → PlaceX l OE R d em

def PlaceCriterionOfIdempotent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra ℤ_[l] R],
    (l : R) ∈ maximalIdeal R → ¬ ((l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (d : ℕ) [NeZero d] (em : ZMod d → OE →+* R),
      (∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) →
      (∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) →
      (∃ ε : OE, (∃ y, ε * ε - ε = (l : OE) * y) ∧ (∀ a, em a ε - 1 ∈ maximalIdeal R) ∧
        ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) → PlaceX l OE R d em

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
