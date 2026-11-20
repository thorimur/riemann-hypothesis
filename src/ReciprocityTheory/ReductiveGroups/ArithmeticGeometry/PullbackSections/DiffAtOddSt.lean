import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.DedekindDomain.Different
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

open NumberField UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

def DiffExpSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (ℓ a m : ℕ), ℓ.Prime → ¬ ℓ ∣ m →
    (discr E).natAbs = ℓ ^ a * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (ℓ : 𝓞 E) ∈ P →
      (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E =
        a * (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P

def DiffAt2St : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (e m : ℕ), Module.finrank ℚ E = 2 ^ (e + 2) → Odd m →
    (discr E).natAbs = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (2 : 𝓞 E) ∈ P →
      ((normalizedFactors (differentIdeal ℤ (𝓞 E))).count P : ℝ) /
          ((normalizedFactors (Ideal.span {(2 : 𝓞 E)})).count P : ℝ) = (e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ e

def DiffAtOddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (e ℓ m : ℕ), ℓ.Prime → Module.finrank ℚ E = 2 ^ (e + 2) →
    ¬ ℓ ∣ m → (discr E).natAbs = ℓ ^ (2 ^ (e + 1)) * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (ℓ : 𝓞 E) ∈ P →
      ((normalizedFactors (differentIdeal ℤ (𝓞 E))).count P : ℝ) /
          ((normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P : ℝ) = 1 / 2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
