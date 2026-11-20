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

noncomputable section

namespace GlobalTheory.FlagPts

variable {k : Type} [Field k] {n : ℕ}

def leadBlock (P : Matrix (Fin n) (Fin n) k) (m : Fin n) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  P.submatrix (Fin.castLE m.isLt) (Fin.castLE m.isLt)

def leadMinor (P : Matrix (Fin n) (Fin n) k) (m : Fin n) : k := (leadBlock P m).det

def luNum (P : Matrix (Fin n) (Fin n) k) (a m : Fin n) : k :=
  ∑ l : Fin (m + 1), P a (Fin.castLE m.isLt l) * (leadBlock P m).cramer (Pi.single (Fin.last m) 1) l

def luLower (P : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := fun a m =>
  if a = m then 1 else if m < a then luNum P a m / leadMinor P m else 0

theorem luLower_apply_self (P : Matrix (Fin n) (Fin n) k) (a : Fin n) : luLower P a a = 1 := by
  simp [luLower]

theorem luLower_apply_of_lt (P : Matrix (Fin n) (Fin n) k) {a m : Fin n} (h : m < a) :
    luLower P a m = luNum P a m / leadMinor P m := by
  simp [luLower, h, h.ne']

theorem luLower_lowerTriangular (P : Matrix (Fin n) (Fin n) k) : (luLower P).BlockTriangular OrderDual.toDual :=
  fun a m h => by
    have h' : a < m := by simpa using h
    simp [luLower, h'.ne, not_lt.2 h'.le]

example (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : leadMinor P (Fin.last n) = P.det := by
  simp [leadMinor, leadBlock]

end GlobalTheory.FlagPts
