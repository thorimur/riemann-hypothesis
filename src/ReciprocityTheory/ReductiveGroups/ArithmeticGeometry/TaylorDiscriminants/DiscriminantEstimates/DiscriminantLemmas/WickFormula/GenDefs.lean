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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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

open MvPolynomial

namespace PI.WickFormula.Gen

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

noncomputable def gdelta (κ : I → J → K) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)

noncomputable def dL (κ : I → J → K) (i : I) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ j, κ i j • (pderiv (Sum.inr j)).toLinearMap

noncomputable def dR (κ : I → J → K) (j : J) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, κ i j • (pderiv (Sum.inl i)).toLinearMap

end

def PowXL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (i : I)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (gdelta κ ^ (n + 1)) (X (Sum.inl i) * R) =
      X (Sum.inl i) * (gdelta κ ^ (n + 1)) R + (n + 1) • dL κ i ((gdelta κ ^ n) R)

def PowXR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (j : J)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (gdelta κ ^ (n + 1)) (X (Sum.inr j) * R) =
      X (Sum.inr j) * (gdelta κ ^ (n + 1)) R + (n + 1) • dR κ j ((gdelta κ ^ n) R)

def CommL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (i : I)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ), (gdelta κ ^ n) (dL κ i R) = dL κ i ((gdelta κ ^ n) R)

def CommR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (j : J)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ), (gdelta κ ^ n) (dR κ j R) = dR κ j ((gdelta κ ^ n) R)

def VanL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (∀ m ∈ R.support, ∑ i, m (Sum.inl i) < n) → (gdelta κ ^ n) R = 0

def VanR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (∀ m ∈ R.support, ∑ j, m (Sum.inr j) < n) → (gdelta κ ^ n) R = 0

end PI.WickFormula.Gen
