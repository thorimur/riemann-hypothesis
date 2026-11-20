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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K R : Type} [Field K] [CommRing R] [Algebra K R] {d : ℕ}

def tpow (t : Fin d → Rˣ) (m : Fin d → ℤ) : R := ((∏ k, t k ^ m k : Rˣ) : R)

def expS (S : Finset (Fin (d + 1))) : Set (Fin d → ℤ) :=
  {m | (∀ k : Fin d, k.succ ∉ S → 0 ≤ m k) ∧ ((0 : Fin (d + 1)) ∉ S → ∑ k, m k ≤ 0)}

variable (K) in

def torusS (t : Fin d → Rˣ) (S : Finset (Fin (d + 1))) : Subalgebra K R := Algebra.adjoin K (tpow t '' expS S)

def jacS (B : Subalgebra K R) (D : Fin d → Derivation K R R) {m : ℕ} (κ : Fin m → Fin d) : AddSubgroup R :=
  AddSubgroup.closure {y | ∃ (b : B) (bs : Fin m → B), y = (b : R) * (Matrix.of fun k l => D (κ k) (bs l)).det}

end CrystallineSemistableComparison.Pb
