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
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def nS (a : ℂ) (i : Fin 3) : ℝ := (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)

def wS (a : ℂ) : ℝ := ((1 + ‖a‖ ^ 2) ^ 2)⁻¹

def blk {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of fun p q : Fin (d + 1) =>
    Fin.cases (Fin.cases e (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => B p' q') q) p

def lin3 (n : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ := ∑ i, X i * C (n i)

def lin4 (n : Fin 3 → ℝ) : MvPolynomial (Option (Fin 3)) ℝ := rename some (lin3 n)

def rowW (u : Fin 2 → ℝ) (v : ℝ) : MvPolynomial (Option (Fin 2)) ℝ :=
  C (u 0) * X (some 0) + C (u 1) * X (some 1) + C v * X none

def evalW (n₀ n₁ : Fin 3 → ℝ) : MvPolynomial (Option (Fin 2)) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ :=
  aeval fun j => Option.elim j (X none) ![lin4 n₀, lin4 n₁]

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
