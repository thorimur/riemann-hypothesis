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
import Mathlib.RingTheory.PowerSeries.Basic
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

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

def LengthQuotientLeOfPowSMul : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (ℓ : O) (e e' : ℕ) (FFs J : Submodule O M),
    Ideal.span {ℓ ^ e} • FFs ≤ J → Ideal.span {ℓ ^ e'} • (⊤ : Submodule O M) ≤ J →
    Module.length O (M ⧸ J) ≤
      Module.length O (M ⧸ (FFs ⊔ Ideal.span {ℓ ^ e'} • (⊤ : Submodule O M))) +
        ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})

def CancelQ : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (a : O) (η b : ℕ) (g : PowerSeries O),
    (X : PowerSeries O) ^ η * g ∈ Ideal.span {C a, (X : PowerSeries O) ^ (b + η)} →
      g ∈ Ideal.span {C a, (X : PowerSeries O) ^ b}

def CancelC : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (a : O) (v t b : ℕ) (g : PowerSeries O), a ≠ 0 → v ≤ t →
    C (a ^ v) * g ∈ Ideal.span {C (a ^ t), (X : PowerSeries O) ^ b} →
      g ∈ Ideal.span {C (a ^ (t - v)), (X : PowerSeries O) ^ b}

def TruncZero : Prop :=
  ∀ (R : Type) [CommRing R] (u π₀ q : R) (ℓ M η y : ℕ), M ≤ y → η ≤ (ℓ - 1) * y →
    (u * π₀ * q ^ (ℓ - 1)) ^ y ∈ Ideal.span {π₀ ^ M * q ^ η}

end Formalism.TruncatedSeriesCounting.R9
