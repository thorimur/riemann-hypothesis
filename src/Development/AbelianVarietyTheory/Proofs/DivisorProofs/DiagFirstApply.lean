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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace GlobalTheory.JacBlock₂

open scoped Matrix

variable {k : Type} [Field k]

def blk {d : ℕ} (i : Fin d) : ℕ := if i.1 = 0 then 0 else if i.1 + 1 = d then 2 else 1

def IsUnipStd {d : ℕ} (u : GL (Fin d) k) : Prop :=
  (∀ i, u.1 i i = 1) ∧ ∀ i j, i ≠ j → ¬ blk i < blk j → u.1 i j = 0

def diagFirst {d : ℕ} (x : kˣ) : GL (Fin d) k where
  val := Matrix.diagonal fun i => if i.1 = 0 then (x : k) else 1
  inv := Matrix.diagonal fun i => if i.1 = 0 then ((x⁻¹ : kˣ) : k) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp

theorem diagFirst_apply {d : ℕ} (x : kˣ) (i j : Fin d) :
    (diagFirst (d := d) x).1 i j = if i = j then (if i.1 = 0 then (x : k) else 1) else 0 := by
  simp [diagFirst, Matrix.diagonal_apply]

end GlobalTheory.JacBlock₂
