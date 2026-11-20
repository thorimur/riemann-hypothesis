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
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IsRadicalAway {R : Type*} [CommRing R] (K : Ideal R) (g : R) : Prop :=
  ∀ f ∈ K.radical, ∃ k : ℕ, g ^ k * f ∈ K

def fibreIdeal {σ : Type*} {n : ℕ} (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ))) (t : σ → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  K.map (MvPolynomial.map (eval t))

theorem fibreIdeal_map_C {σ : Type*} {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (t : σ → ℂ) :
    fibreIdeal (J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ))) t = J := by
  have h : (MvPolynomial.map (eval t)).comp (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ)) =
      RingHom.id (MvPolynomial (Fin n) ℂ) := by
    ext p <;> simp
  rw [fibreIdeal, Ideal.map_map, h, Ideal.map_id]

def GenericFibreRadicalAway.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (n : ℕ) (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ)))
    (g : MvPolynomial (Fin n) (MvPolynomial σ ℂ)), IsRadicalAway K g →
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      IsRadicalAway (fibreIdeal K t) (MvPolynomial.map (eval t) g)

end

end GroundTheory.Heights₂.Heights
