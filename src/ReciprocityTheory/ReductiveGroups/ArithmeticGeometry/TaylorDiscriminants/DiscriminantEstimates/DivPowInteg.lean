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

namespace PI

namespace DivPowInteg

noncomputable def delta {K I J : Type} [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) :
    MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)

end DivPowInteg

def DivPowInteg : Prop :=
  ∀ (A K I J : Type) [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
    [Fintype I] [Fintype J] (L : Submodule A K) (κ : I → J → K),
    (∀ i j, κ i j ∈ L) →
    ∀ (P : MvPolynomial (I ⊕ J) A) (n : ℕ),
      (∀ m, (((n.factorial : ℚ)⁻¹ •
          (DivPowInteg.delta κ ^ n) (MvPolynomial.map (algebraMap A K) P)).coeff m) ∈ L ^ n) ∧
      (((∀ m ∈ P.support, ∑ i, m (Sum.inl i) < n) ∨ (∀ m ∈ P.support, ∑ j, m (Sum.inr j) < n)) →
        (DivPowInteg.delta κ ^ n) (MvPolynomial.map (algebraMap A K) P) = 0)

end PI
