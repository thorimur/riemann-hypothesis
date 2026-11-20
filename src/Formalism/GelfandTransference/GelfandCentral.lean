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

open Finset

noncomputable section

namespace Formalism.HadamardInequality

def GlRel {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)

def epow {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0, a, b => if a = b then 1 else 0
  | k + 1, a, b => ∑ c, E a c * epow E k c b

def etr {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) : A := ∑ a, epow E k a a

def GelfandCentral : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (k : ℕ) (c d : Fin n), etr E k * E c d = E c d * etr E k

def HighestDiag : Prop :=
  ∀ (A M : Type) [Ring A] [AddCommGroup M] [Module A M] (n : ℕ) (E : Fin n → Fin n → A),
    GlRel E → ∀ (ν : Fin n → ℤ) (v : M),
    (∀ a b : Fin n, a < b → E a b • v = 0) → (∀ a : Fin n, E a a • v = ν a • v) →
    ∀ (k : ℕ) (a : Fin n),
      epow E (k + 1) a a • v =
        (ν a + (n : ℤ) - 1 - (a : ℤ)) • (epow E k a a • v) -
          ∑ b ∈ univ.filter (fun b : Fin n => a < b), epow E k b b • v

end Formalism.HadamardInequality
