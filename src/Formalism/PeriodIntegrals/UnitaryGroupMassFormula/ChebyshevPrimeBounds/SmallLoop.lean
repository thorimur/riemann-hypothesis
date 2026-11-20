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

namespace PI.PC

def tst (n c : Nat) : Bool :=
  Nat.blt (n ^ 256) (2 ^ ((3225600000000 * n - 1) / (c * 6931471808)))

def force (x : Nat) (f : Nat → Bool) : Bool :=
  match x with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem force_eq (x : Nat) (f : Nat → Bool) : force x f = f x := by
  cases x <;> rfl

def loop (B : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | k + 1, n, c, Q =>
    force n fun n => force c fun c => force Q fun Q =>
    if Nat.gcd n Q = 1 then
      tst n (c + 1) && loop B k (n + 1) (c + 1) (if n ≤ B then Q * n else Q)
    else tst n c && loop B k (n + 1) c Q

theorem loop_run : loop 362 131070 2 0 1 = true := by decide +kernel

end PI.PC
