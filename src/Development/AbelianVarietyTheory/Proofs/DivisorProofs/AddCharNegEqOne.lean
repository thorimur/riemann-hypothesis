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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem addChar_neg_eq_one {A : Type} [AddGroup A] (ψ : AddChar A ℂ) {x : A} (h : ψ x = 1) : ψ (-x) = 1 := by
  have e := AddChar.map_add_eq_mul ψ (-x) x
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at e
  exact e.symm

variable {k : Type} [Field k] [ValuativeRel k]

def latt (ψ0 : AddChar k ℂ) (n d : ℕ) (s : k) : AddSubgroup (Matrix (Fin n) (Fin d) k) where
  carrier := {Y | ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1}
  add_mem' := by
    intro a b ha hb i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.add_apply, mul_add, AddChar.map_add_eq_mul] at *
    rw [ha i j o ho, hb i j o ho, one_mul]
  zero_mem' := by
    intro i j o _
    simp
  neg_mem' := by
    intro a ha i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.neg_apply, mul_neg] at *
    exact addChar_neg_eq_one ψ0 (ha i j o ho)

theorem mem_latt {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k} {Y : Matrix (Fin n) (Fin d) k} :
    Y ∈ latt ψ0 n d s ↔ ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1 := Iff.rfl

open Classical in

def cind {X : Type} [AddGroup X] (L : AddSubgroup X) (y : X) : X → ℂ := fun Y => if Y - y ∈ L then 1 else 0

end GlobalTheory.LinSchur
