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

namespace GlobalTheory.PsChar

variable {M A : Type*} [Monoid M] [CommRing A]

noncomputable def alt (T : M → A) : (n : ℕ) → (Fin n → M) → A
  | 0, _ => 1
  | n + 1, x => T (x 0) * alt T n (Fin.tail x) - ∑ i : Fin n, alt T n (Function.update (Fin.tail x) i (x 0 * Fin.tail x i))

structure IsPsChar (d : ℕ) (T : M → A) : Prop where
  one : T 1 = d
  comm : ∀ x y, T (x * y) = T (y * x)
  alt_eq_zero : ∀ x : Fin (d + 1) → M, alt T (d + 1) x = 0

theorem map_alt {B : Type*} [CommRing B] (f : A →+* B) (T : M → A) :
    ∀ (n : ℕ) (x : Fin n → M), f (alt T n x) = alt (fun g => f (T g)) n x
  | 0, _ => by simp [alt]
  | n + 1, x => by simp [alt, map_alt f T n]

end GlobalTheory.PsChar
