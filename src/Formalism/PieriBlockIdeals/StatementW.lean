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
import Mathlib.GroupTheory.Coxeter.Inversion
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

namespace Formalism.CohomologicalDescent

open CoxeterSystem

universe u v

def InvSeqAll : Prop :=
  ∀ (B : Type u) (W : Type v) [Group W] (M : CoxeterMatrix B) (cs : CoxeterSystem M W) (w₀ : W),
    (∀ w : W, cs.length w ≤ cs.length w₀) →
    ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = w₀ →
      (cs.rightInvSeq ω).Nodup ∧ (∀ t : W, t ∈ cs.rightInvSeq ω ↔ cs.IsReflection t) ∧
      (cs.leftInvSeq ω).Nodup ∧ (∀ t : W, t ∈ cs.leftInvSeq ω ↔ cs.IsReflection t) ∧
      ω.length = Nat.card {t : W // cs.IsReflection t}

def adjSwap {n : ℕ} (a : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap a.castSucc a.succ

def wordPerm {n : ℕ} (ω : List (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (ω.map adjSwap).prod

def rightInvSeqA {n : ℕ} : List (Fin n) → List (Equiv.Perm (Fin (n + 1)))
  | [] => []
  | a :: ω => (wordPerm ω)⁻¹ * adjSwap a * wordPerm ω :: rightInvSeqA ω

def InvSeqAllTypeA : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)), wordPerm ω = Fin.revPerm →
    (∀ ω' : List (Fin n), wordPerm ω' = Fin.revPerm → ω.length ≤ ω'.length) →
      (rightInvSeqA ω).Nodup ∧
      (∀ t : Equiv.Perm (Fin (n + 1)),
        t ∈ rightInvSeqA ω ↔ ∃ i j : Fin (n + 1), i < j ∧ t = Equiv.swap i j) ∧
      ω.length = (n + 1).choose 2

def InvSeqOddTypeA : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)), wordPerm ω = Fin.revPerm →
    (∀ i j : Fin (n + 1), i < j → Odd ((rightInvSeqA ω).count (Equiv.swap i j))) ∧
      (n + 1).choose 2 ≤ ω.length

end Formalism.CohomologicalDescent
