import Mathlib.Algebra.Group.Pi.Units
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

open Matrix

namespace PositivityTheory.KB.PsiBlockMatrix

variable (R : Type) [CommRing R]

def ee (q n : ℕ) : Fin n × Fin q ≃ Fin (q * n) := (Equiv.prodComm _ _).trans finProdFinEquiv

def blkM (q n : ℕ) : (Fin q → Matrix (Fin n) (Fin n) R) →* Matrix (Fin (q * n)) (Fin (q * n)) R where
  toFun a := Matrix.reindex (ee q n) (ee q n) (Matrix.blockDiagonal a)
  map_one' := by simp
  map_mul' a b := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    rfl

def blk (q n : ℕ) : (Fin q → GL (Fin n) R) →* GL (Fin (q * n)) R :=
  (Units.map (blkM R q n)).comp MulEquiv.piUnits.symm.toMonoidHom

end PositivityTheory.KB.PsiBlockMatrix
