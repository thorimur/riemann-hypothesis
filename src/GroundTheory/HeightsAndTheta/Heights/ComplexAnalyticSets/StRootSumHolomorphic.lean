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
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def RootSumHolomorphic.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (W : Set (Fin d → ℂ)) (Φ : (Fin d → ℂ) → ℂ → ℂ),
    m.Monic → IsOpen W → (∀ y ∈ W, (m.map (MvPolynomial.eval y)).Separable) →
    (∀ y ∈ W, ∀ τ : ℂ, (m.map (MvPolynomial.eval y)).IsRoot τ →
      ∃ O : Set ((Fin d → ℂ) × ℂ), IsOpen O ∧ (y, τ) ∈ O ∧ ∃ Ψ : (Fin d → ℂ) × ℂ → ℂ,
        DifferentiableOn ℂ Ψ O ∧
        ∀ p ∈ O, (m.map (MvPolynomial.eval p.1)).IsRoot p.2 → Φ p.1 p.2 = Ψ p) →
    DifferentiableOn ℂ (fun y => ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum) W

end

end GroundTheory.Heights₂.Heights.ComplexSets
