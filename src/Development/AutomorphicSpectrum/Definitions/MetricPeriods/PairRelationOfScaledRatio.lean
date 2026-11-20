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

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial

def formPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) : MvPolynomial σ ℝ :=
  ∑ w : Fin n → σ, C (a w) * ∏ j, X (w j)

variable {Ψ : Type} {N : ℕ}

def gapX (p : Ψ × Fin N) : MvPolynomial (Ψ × Fin N) ℝ :=
  X p - if h : (p.2 : ℕ) + 1 < N then X (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0

def gap (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) : ℝ := eval lam (gapX p)

def Dominant (lam : Ψ × Fin N → ℝ) : Prop := ∀ p : Ψ × Fin N, (p.2 : ℕ) + 1 < N → 0 ≤ gap lam p

def toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ := aeval gapX

def toWtS : MvPolynomial (Option (Ψ × Fin N)) ℝ →ₐ[ℝ] MvPolynomial (Option (Ψ × Fin N)) ℝ :=
  aeval fun o : Option (Ψ × Fin N) => o.elim (X none) fun p => rename some (gapX p)

def gapS (lam : Ψ × Fin N → ℝ) (s : ℝ) : Option (Ψ × Fin N) → ℝ := fun o => o.elim s (gap lam)

def xiCoef [DecidableEq Ψ] (τ : Ψ) (a : Fin N) (p : Ψ × Fin N) : ℤ :=
  if p.1 = τ then
    (if (p.2 : ℕ) + 1 = a then 1 else 0) + (if (p.2 : ℕ) = a + 1 then 1 else 0) - (if p.2 = a then 2 else 0)
  else 0

def linePoly {σ : Type} (c : σ → ℝ) (e : σ → ℤ) (Q : MvPolynomial σ ℝ) : Polynomial ℝ :=
  aeval (fun a => Polynomial.C (c a) - Polynomial.C ((e a : ℝ) / 2) * Polynomial.X) Q

def rhoWt (Ψ : Type) (N : ℕ) : Ψ × Fin N → ℝ := fun p => -((p.2 : ℕ) : ℝ)

end GlobalTheory.CompanionTheory.Ar.PB
