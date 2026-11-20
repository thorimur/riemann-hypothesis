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

namespace PI.PrimesDyadicRS.K

def force (x : Nat) (f : Nat → Bool) : Bool :=
  match x with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem force_eq (x : Nat) (f : Nat → Bool) : force x f = f x := by
  cases x <;> rfl

def tstR (h d : Nat) : Bool :=
  Nat.blt 0 d && Nat.ble (2 ^ (7680000000000 * (h + 1) / (10 * d * 6931471803) + 257)) (h ^ 256)

def pr (Q m : Nat) : Nat :=
  if m ≤ 362 then (if Nat.gcd m (Nat.factorial (m - 1)) = 1 then 1 else 0)
  else (if Nat.gcd m Q = 1 then 1 else 0)

def nxt (Q h d : Nat) : Nat :=
  d + pr Q (h + 1) - (if (h + 1) % 2 = 0 then pr Q ((h + 1) / 2) else 0)

def loop (Q hT dT : Nat) : Nat → Nat → Nat → Bool
  | 0, h, d => h == hT && d == dT
  | k + 1, h, d =>
    force h fun h => force d fun d =>
    (Nat.blt h 41 || tstR h d) && loop Q hT dT k (h + 1) (nxt Q h d)

def run (hT dT k h d : Nat) : Bool :=
  force (Nat.factorial 362) fun Q => loop Q hT dT k h d

end PI.PrimesDyadicRS.K
