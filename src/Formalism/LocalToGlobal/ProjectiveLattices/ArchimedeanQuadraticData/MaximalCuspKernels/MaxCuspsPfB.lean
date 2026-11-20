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

open MeasureTheory Complex

namespace Formalism.L2.Pj.QAt

abbrev mcBox (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ : Fin n => Set.Ioc (0 : ℝ) 1

def mcE {n : ℕ} (m : Fin n → ℤ) (u : Fin n → ℝ) : ℂ :=
  cexp (-(2 * Real.pi * I) * ∑ j, (m j : ℂ) * (u j : ℂ))

def mcCo {n : ℕ} (g : (Fin n → ℝ) → ℂ) (m : Fin n → ℤ) : ℂ := ∫ u in mcBox n, g u * mcE m u

def mcT {n N : ℕ} (c : Fin n → Fin N → ℤ) (t : Fin n → ℝ) : Fin N → ℝ :=
  fun i => ∑ j, t j * (c j i : ℝ)

def mcG {n N : ℕ} (g : (Fin N → ℝ) → ℂ) (c : Fin n → Fin N → ℤ) (k : Fin n → ℤ)
    (u : Fin N → ℝ) : ℂ :=
  mcCo (fun t => g (u + mcT c t)) k

end Formalism.L2.Pj.QAt
