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
import Mathlib.RingTheory.PowerSeries.Basic
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

noncomputable section

namespace LevelStatements.Lv

open PowerSeries

def PsCycloStatement : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ), l.Prime → ∀ (φ : PowerSeries O →ₐ[O] PowerSeries O),
    φ X = (1 + X) ^ l - 1 → ∀ (q : PowerSeries O) (w : (PowerSeries O)ˣ),
    q = (w : PowerSeries O) * (((Polynomial.cyclotomic l O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) →
    ∀ s : ℕ, ∃ w' : (PowerSeries O)ˣ, (⇑φ)^[s] q = (w' : PowerSeries O) *
      (((Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O)

end LevelStatements.Lv
