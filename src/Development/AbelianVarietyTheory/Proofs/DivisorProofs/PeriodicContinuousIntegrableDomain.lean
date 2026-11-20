import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

theorem integrableOn_fundamentalDomain_of_periodic :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (F : (Fin g → ℂ) → ℝ)
      (Fd : Set (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Continuous F →
      (∀ (l : Λ) z, F (z + l) = F z) → IsAddFundamentalDomain Λ Fd volume →
      IntegrableOn F Fd volume := by
  intro g Λ _ F Fd hspan hF hper hFd
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  haveI : MeasurableVAdd Λ (Fin g → ℂ) :=
    (inferInstance : MeasurableVAdd Λ.toAddSubgroup (Fin g → ℂ))
  haveI : VAddInvariantMeasure Λ (Fin g → ℂ) volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup (Fin g → ℂ) volume)
  let b := Module.Free.chooseBasis ℤ Λ
  have hP := ZLattice.isAddFundamentalDomain b (volume : Measure (Fin g → ℂ))
  have hinv : ∀ (l : Λ) (x : Fin g → ℂ), F (l +ᵥ x) = F x := by
    intro l x
    rw [Submodule.vadd_def, vadd_eq_add, add_comm]
    exact hper l x
  rw [hFd.integrableOn_iff hP hinv]
  have hbdd := ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ))) :=
    hbdd.isCompact_closure
  exact (hF.continuousOn.integrableOn_compact hcpt).mono_set subset_closure

end GlobalTheory
