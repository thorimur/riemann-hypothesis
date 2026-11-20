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

namespace Formalism.RankGapBounds.ExistsSmulMemTer

abbrev G0 := ZMod 2 × ZMod 2
abbrev GG (e : ℕ) := G0 × ZMod (2 ^ e)

def sg : G0 := (1, 0)
def c0 : G0 := (0, 1)
def cc (e : ℕ) : GG e := (c0, 0)

def InPhi {e : ℕ} (γ : GG e) : Prop := γ.1.2 = 0

def place {e : ℕ} (γ : GG e) : GG e := if γ.1.2 = 0 then γ else γ + cc e

def OrbitParity : Prop :=
  ∀ (e : ℕ) (φ τ : GG e) (i : ℕ), φ.1.2 = 1 → InPhi τ → (InPhi (i • φ + τ) ↔ Even i)

def OrbitCoord : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ), (place (i • φ + ((0 : G0), t))).2 = t + i • φ.2

def OrbitOver : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ),
    (φ.1 = c0 → (place (i • φ + ((0 : G0), t))).1 = 0) ∧
    (φ.1 = sg + c0 → (place (i • φ + ((0 : G0), t))).1 = if Even i then 0 else sg)

def ConjInOrbit : Prop :=
  ∀ (e : ℕ) (φ : GG e), φ.1.2 = 1 → (cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e)

def OrbitCard : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)), φ.1 = c0 → φ.2 ≠ 0 →
    (Set.range fun i : ℕ => place (i • φ + ((0 : G0), t))).ncard = addOrderOf φ.2 ∧
    Even (addOrderOf φ.2)

end Formalism.RankGapBounds.ExistsSmulMemTer
