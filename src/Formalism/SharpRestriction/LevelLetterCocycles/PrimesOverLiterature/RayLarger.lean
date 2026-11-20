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

namespace Formalism.MainNotions.N.Lit.RayLarger

open NumberField IsDedekindDomain

abbrev Qb : Type := AlgebraicClosure ℚ

abbrev Fld : Type := IntermediateField ℚ Qb

def primesOver (L : Fld) (p : ℕ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {v | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}

def SplitsCompletely (L : Fld) (p : ℕ) : Prop :=
  (primesOver L p).ncard = Module.finrank ℚ L

def IsRayPrime (K : Fld) (m p : ℕ) : Prop :=
  p.Prime ∧ ∃ π : Qb, π ∈ K ∧ IsIntegral ℤ π ∧ IsIntegral ℤ ((π - 1) / (m : Qb)) ∧
    ∃ σ : Qb →ₐ[ℚ] Qb, π * σ π = (p : Qb)

def Admissible (K : Fld) (m : ℕ) (L : Fld) : Prop :=
  K ≤ L ∧ FiniteDimensional ℚ L ∧ ∀ p, IsRayPrime K m p → SplitsCompletely L p

def Stmt : Prop :=
  ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
    (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
    ∃ (p : ℕ) (L : Fld), p.Prime ∧ ¬ p ∣ m ∧
      (∃ π : Qb, π ∈ K ∧ IsIntegral ℤ π ∧ ∃ σ : Qb →ₐ[ℚ] Qb, π * σ π = (p : Qb)) ∧
      Admissible K m L ∧ ¬ SplitsCompletely L p

example : 0 < (1 : ℕ) ∧ 0 < (4 : ℕ) ∧ 4 * 1 ∣ (4 : ℕ) := by decide

end Formalism.MainNotions.N.Lit.RayLarger
