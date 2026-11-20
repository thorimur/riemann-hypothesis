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

namespace Formalism.NOK

open scoped ENNReal

def gaussV {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ)
    (f : PowerSeries O) : ℝ≥0∞ :=
  ⨅ n : ℕ, (((IsDiscreteValuationRing.addVal O (PowerSeries.coeff n f) : ℕ∞)) : ℝ≥0∞) +
    ENNReal.ofReal (x * n)

def GaussMul : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 < x →
    ∀ f g : PowerSeries O, gaussV x (f * g) = gaussV x f + gaussV x g

def GaussAdd : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ),
    ∀ f g : PowerSeries O, min (gaussV x f) (gaussV x g) ≤ gaussV x (f + g)

def GaussC : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 ≤ x →
    ∀ c : O, gaussV x (PowerSeries.C c) =
      ((IsDiscreteValuationRing.addVal O c : ℕ∞) : ℝ≥0∞)

def GaussUnit : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 ≤ x →
    ∀ u : PowerSeries O, IsUnit u → gaussV x u = 0

def GaussEis : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (x : ℝ), 0 ≤ x → ∀ (E : Polynomial O) (N : ℕ), 1 ≤ N →
      E.IsEisensteinAt (Ideal.span {ϖ}) → E.natDegree = N →
      gaussV x (E : PowerSeries O) = ENNReal.ofReal (min 1 (x * N))

end Formalism.NOK
