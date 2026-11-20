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

namespace ReciprocityTheory.Coh.EulerCharacteristicLength

universe u

variable {R : Type u} [CommRing R]

open Function

section LES

variable {a b c : ℕ → Type u} [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)]
  [∀ n, AddCommGroup (b n)] [∀ n, Module R (b n)] [∀ n, AddCommGroup (c n)] [∀ n, Module R (c n)]
  (f : ∀ n, a n →ₗ[R] b n) (g : ∀ n, b n →ₗ[R] c n) (δ : ∀ n, c n →ₗ[R] a (n + 1))

end LES

def FL (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : Prop :=
  (∀ n, Module.length R (a n) ≠ ⊤) ∧ ∀ n, N < n → Module.length R (a n) = 0

noncomputable def ch (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * ((Module.length R (a n)).toNat : ℤ)

section LES2

variable {a b c : ℕ → Type u} [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)]
  [∀ n, AddCommGroup (b n)] [∀ n, Module R (b n)] [∀ n, AddCommGroup (c n)] [∀ n, Module R (c n)]
  (f : ∀ n, a n →ₗ[R] b n) (g : ∀ n, b n →ₗ[R] c n) (δ : ∀ n, c n →ₗ[R] a (n + 1))
  (h0 : Injective (f 0)) (hB : ∀ n, Exact (f n) (g n)) (hC : ∀ n, Exact (g n) (δ n))
  (hA : ∀ n, Exact (δ n) (f (n + 1)))
include h0 hB hC hA

end LES2

end ReciprocityTheory.Coh.EulerCharacteristicLength
