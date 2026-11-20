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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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

open MvPolynomial

namespace GlobalTheory.CayleyBlock

def dList {σ : Type} [DecidableEq σ] (l : List σ) : Module.End ℂ (MvPolynomial σ ℂ) :=
  (l.map fun v => ((pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
    MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)).prod

def smallList {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : List (Fin p × Fin p) :=
  (List.finRange q).flatMap fun b => (List.finRange p).map fun j => (τ b j, j)

def bigList {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : List (Fin q × Fin p × Fin p) :=
  (List.finRange q).flatMap fun b => (List.finRange p).map fun j => (b, τ b j, j)

def blockGraph {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : Fin q × Fin p × Fin p →₀ ℕ :=
  ∑ b, ∑ j, Finsupp.single (b, τ b j, j) 1

def sumMap (p q : ℕ) : MvPolynomial (Fin p × Fin p) ℂ →ₐ[ℂ] MvPolynomial (Fin q × Fin p × Fin p) ℂ :=
  aeval fun x => ∑ b, X (b, x.1, x.2)

def blockEmb {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    Fin q × Fin p × Fin p → Fin (p * q) × Fin (p * q) :=
  fun x => (Fintype.equivFinOfCardEq h1 ((), x.2.1, x.1), Fintype.equivFinOfCardEq h1 ((), x.2.2, x.1))

def sgnProd {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : ℤ := ((∏ b, Equiv.Perm.sign (τ b) : ℤˣ) : ℤ)

end GlobalTheory.CayleyBlock
