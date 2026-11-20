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
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

def FiniteCoverPuncturedPolydisc.Statement : Prop :=
  ∀ (e N : ℕ) (c : Fin (e + 1) → ℂ) (r : ℝ) (Y : Type) [TopologicalSpace Y]
    (p : Y → ↥(Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})),
    0 < r → c 0 = 0 → IsCoveringMap p → (∀ z, (p ⁻¹' {z}).encard = N) →
    ∃ (m : ℕ) (ord : Fin m → ℕ) (δ : ℝ)
      (ψ : Fin m → ↥(Metric.ball c δ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) → Y),
      0 < δ ∧ δ ≤ 1 ∧ ∑ b, ord b = N ∧ (∀ b, 1 ≤ ord b) ∧ (∀ b, Continuous (ψ b)) ∧
      (∀ b t, ((p (ψ b t) : Fin (e + 1) → ℂ)) =
        Function.update (t : Fin (e + 1) → ℂ) 0 ((t : Fin (e + 1) → ℂ) 0 ^ ord b)) ∧
      (∀ b, Function.Injective (ψ b)) ∧
      (∀ b b', b ≠ b' → ∀ t t', ψ b t ≠ ψ b' t') ∧
      (∀ y, dist ((p y : Fin (e + 1) → ℂ)) c < δ ^ N → ∃ b t, ψ b t = y)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
