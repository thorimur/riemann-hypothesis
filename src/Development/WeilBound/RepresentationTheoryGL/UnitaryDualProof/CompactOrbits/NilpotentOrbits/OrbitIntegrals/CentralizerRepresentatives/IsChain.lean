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

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

section Chain

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

def IsChain (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W) : Prop :=
  ∀ a (i : Fin (l a)), N (B ⟨a, i⟩) = if h : (i : ℕ) + 1 < l a then B ⟨a, ⟨i + 1, h⟩⟩ else 0

end Chain

variable {k : Type} [Field k] {n : ℕ}

structure Frame (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (M : Type) [Fintype M] (L : M → Type)
    [∀ m, Fintype (L m)] (R : Z → (m : M) → L m → L m → k) (o : (m : M) → L m → k)
    (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k) where
  ι : M → Type
  [fι : ∀ m, Fintype (ι m)]
  l : (m : M) → ι m → ℕ
  s : (m : M) → ι m → ℕ
  β : Module.Basis (Σ m, L m × (Σ a : ι m, Fin (l m a))) k (Fin n → k)
  hl : ∀ m a, 0 < l m a
  hs : ∀ m a, s m a ≤ l m a
  hZ : ∀ (z : Z) m (p : L m) (j : Σ a : ι m, Fin (l m a)),
    (z : Matrix (Fin n) (Fin n) k) *ᵥ β ⟨m, (p, j)⟩ = ∑ q, R z m p q • β ⟨m, (q, j)⟩
  hN : ∀ m (p : L m) (a : ι m) (i : Fin (l m a)), N *ᵥ β ⟨m, (p, ⟨a, i⟩)⟩ =
    if h : (i : ℕ) + 1 < l m a then β ⟨m, (p, ⟨a, ⟨i + 1, h⟩⟩)⟩ else 0
  hv : v = ∑ m, ∑ p, ∑ a, if h : s m a < l m a then o m p • β ⟨m, (p, ⟨a, ⟨s m a, h⟩⟩)⟩ else 0
  hA : ∀ A : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * A = A * z) → A * N = N * A →
    ∀ m (p : L m) (a : ι m) (i : Fin (l m a)), (i : ℕ) < s m a → β.repr (A *ᵥ v) ⟨m, (p, ⟨a, i⟩)⟩ = 0

attribute [instance] Frame.fι

end PositivityTheory.RgUd.T.Nil.Orb.BReps
