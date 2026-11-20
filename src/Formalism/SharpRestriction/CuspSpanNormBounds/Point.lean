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

namespace Formalism.MainNotions.S

def ptEntry {K : Type*} [Zero K] : List (K × ℕ) → ℕ → ℕ → K
  | [], _, _ => 0
  | (t, s) :: bs, i, j =>
    if i < s ∧ j < s then (if i + j + 1 = s then t else 0)
    else if s ≤ i ∧ s ≤ j then ptEntry bs (i - s) (j - s) else 0

def Point (K : Type*) [Zero K] (i : ℕ) : Type _ :=
  {bs : List (K × ℕ) // (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) ∧ (bs.map Prod.snd).sum = i}

def ptMat {K : Type*} [Zero K] {i : ℕ} (p : Point K i) : Matrix (Fin i) (Fin i) K :=
  fun a b => ptEntry p.1 a.val b.val

end Formalism.MainNotions.S
