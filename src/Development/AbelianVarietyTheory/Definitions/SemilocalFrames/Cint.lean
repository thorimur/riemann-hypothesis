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
open scoped Classical

namespace GlobalTheory.IdxInt

variable {W : Type} [AddCommGroup W]

def Fine (A : AddSubgroup W) (φ : W → ℂ) (B : AddSubgroup W) : Prop :=
  B ≤ A ∧ B.relIndex A ≠ 0 ∧ (∀ w, ∀ b ∈ B, φ (w + b) = φ w) ∧
    ((fun w => (QuotientAddGroup.mk w : W ⧸ B)) '' Function.support φ).Finite

def Nice (A : AddSubgroup W) (φ : W → ℂ) : Prop := ∃ B, Fine A φ B

def cint (A : AddSubgroup W) (φ : W → ℂ) : ℂ :=
  if h : Nice A φ then (∑ᶠ c : W ⧸ h.choose, φ c.out) / (h.choose.relIndex A : ℂ) else 0

def ind (P : W → Prop) : W → ℂ := fun w => if P w then 1 else 0

end GlobalTheory.IdxInt
