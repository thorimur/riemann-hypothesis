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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.PadicNumbers
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

open ValuativeRel

namespace PI.LocDualGen.W

def PsiKer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (t : ℚ_[l]) (a : ℚ), (∃ n : ℕ, a.den = l ^ n) → ‖t - (a : ℚ_[l])‖ ≤ 1 →
    (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ ‖t‖ ≤ 1)

def FpDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K]

def FpDualUnram : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    Irreducible ((l : ℕ) : 𝒪[K]) →
    ∀ a : K, (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K))‖ ≤ 1) ↔ a ∈ 𝒪[K]

def EpSelfDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (L : Type) [CommRing L]
    [Algebra K L], IsNonarchimedeanLocalField K → CharZero K →
    Module.Free K L → Module.finrank K L = 2 → IsReduced L →
    ∀ O : Subring L, (∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x) →
    (∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)}) →
    ∀ x : L, (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O

end PI.LocDualGen.W
