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

namespace PI.LatLocGlob

def loc {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (p : Ideal R) (L : Submodule R V) : Set V :=
  {x | ∃ s : R, s ∉ p ∧ s • x ∈ L}

def IsFullLat (K : Type) {R V : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] (L : Submodule R V) : Prop :=
  L.FG ∧ Submodule.span K (L : Set V) = ⊤

def LatLocGlob : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (L0 : Submodule R V), IsFullLat K L0 →
    ∀ M : Ideal R → Set V,
      (∀ p : Ideal R, p.IsMaximal → ∃ N : Submodule R V, IsFullLat K N ∧ M p = loc p N) →
      Set.Finite {p : Ideal R | p.IsMaximal ∧ M p ≠ loc p L0} →
      ∃! L : Submodule R V, IsFullLat K L ∧ ∀ p : Ideal R, p.IsMaximal → loc p L = M p

end PI.LatLocGlob
