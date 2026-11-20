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

set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial

namespace GlobalTheory.FibLine

def fsDens (x : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)

def lineVec (x : ℂ) : Fin 2 → ℂ := ![1, x]

def qCoef (x : ℂ) (ab : Fin 2 × Fin 2) : ℂ :=
  lineVec x ab.2 * starRingEnd ℂ (lineVec x ab.1) / ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)

def entries {R : Type} (H : Matrix (Fin 2) (Fin 2) R) : Fin 2 × Fin 2 → R := fun ab => H ab.1 ab.2

def qMat {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (x : ℂ) : R :=
  ∑ ab : Fin 2 × Fin 2, qCoef x ab • entries H ab

def fibPow (k : ℕ) : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  ∑ f : Fin k → Fin 2 × Fin 2, C (∫ x : ℂ, (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) * ∏ i, X (f i)

def hPoly (k : ℕ) : MvPolynomial (Fin 2) ℂ :=
  (Nat.rec (motive := fun _ => MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ) (1, X 0)
    (fun _ p => (p.2, X 0 * p.2 - X 1 * p.1)) k).1

theorem hPoly_zero : hPoly 0 = 1 := rfl

theorem hPoly_one : hPoly 1 = X 0 := rfl

theorem hPoly_add_two (k : ℕ) : hPoly (k + 2) = X 0 * hPoly (k + 1) - X 1 * hPoly k := rfl

def trDet : Fin 2 → MvPolynomial (Fin 2 × Fin 2) ℂ :=
  ![X (0, 0) + X (1, 1), X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)]

end GlobalTheory.FibLine
