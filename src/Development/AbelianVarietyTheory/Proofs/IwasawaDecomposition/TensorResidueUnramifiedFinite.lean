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
import Mathlib.RingTheory.RingHom.Unramified
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
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem tensor_quot_maximalIdeal_finite_formallyUnramified :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B]
      [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite →
      ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified →
      Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧
      Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by
  intro A B R _ _ _ _ _ _ hfin hfu
  have hf : Module.Finite A (R ⧸ maximalIdeal R) := by
    rw [← RingHom.finite_algebraMap]; exact hfin
  have hu : Algebra.FormallyUnramified A (R ⧸ maximalIdeal R) := by
    rw [← RingHom.formallyUnramified_algebraMap]; exact hfu
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) B R B (maximalIdeal R)
  haveI : Algebra.FormallyUnramified B (B ⊗[A] (R ⧸ maximalIdeal R)) :=
    Algebra.FormallyUnramified.base_change B
  haveI : Module.Finite B (B ⊗[A] (R ⧸ maximalIdeal R)) := Module.Finite.base_change A B _
  exact ⟨Algebra.FormallyUnramified.of_equiv e, Module.Finite.equiv e.toLinearEquiv⟩

end GlobalTheory
