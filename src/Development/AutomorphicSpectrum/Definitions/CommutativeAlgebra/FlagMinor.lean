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

namespace GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

def LocFree (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E) : Prop :=
  (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) ∧
  ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ R) ∧ (∀ l, c l ∈ R) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ L) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q

def spanOver (R : Subalgebra o Ω) (S : Set E) : AddSubgroup E :=
  AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ S, v = a • e}

def GenDual (R : Subalgebra o Ω) (L : AddSubgroup E) {M : ℕ} (φ : Fin M → Module.Dual Ω E) : Prop :=
  (∀ l, ∀ v ∈ L, φ l v ∈ R) ∧
  ∀ ψ : Module.Dual Ω E, (∀ v ∈ L, ψ v ∈ R) → ∃ u : Fin M → Ω, (∀ l, u l ∈ R) ∧ ψ = ∑ l, u l • φ l

noncomputable def flagMinor {N M : ℕ} (φ : Fin M → Module.Dual Ω E) (w : Fin N → E) (i : ℕ) (hi : i ≤ N)
    (I : Fin i → Fin M) : Ω :=
  Matrix.det (Matrix.of fun a b : Fin i => φ (I a) (w (Fin.castLE hi b)))

end GlobalTheory.CompanionTheory.Ar.Num
