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
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace Formalism.L2.Props

open Filter Topology IsDedekindDomain NumberField

def LogCycConv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ L : ℚ_[l],
    Tendsto (fun k : ℕ => ((((u : ℤ_[l]) : ℚ_[l]) ^ ((l - 1) * l ^ k) - 1) / (((l - 1) * l ^ k : ℕ) : ℚ_[l])))
      atTop (𝓝 L)

def PlaceEmbExists : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    (∀ x : F, algebraMap F Ω x ∈ A ↔ v.valuation F x ≤ 1) →
    ∃ i : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F), ∀ x : Ω, x ∈ A ↔
      ∃ q : Polynomial (v.adicCompletion F), q.Monic ∧ (∀ k, q.coeff k ∈ v.adicCompletionIntegers F) ∧
        Polynomial.aeval (i x) q = 0

def IntAdelesCompactOpen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} ∧
    IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

def TameTrivOnZ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime →
    Nat.card (𝓞 E ⧸ v.asIdeal) = g →
    ∀ ξ : (v.adicCompletion E)ˣ →* ℂˣ,
      (∀ u : (v.adicCompletion E)ˣ, Valued.v ((u : v.adicCompletion E) - 1) < 1 → ξ u = 1) →
      (∀ (m : ℤ) (u : (v.adicCompletion E)ˣ), ¬ (g : ℤ) ∣ m → (u : v.adicCompletion E) = (m : v.adicCompletion E) → ξ u = 1) →
      ∀ u : (v.adicCompletion E)ˣ, Valued.v (u : v.adicCompletion E) = 1 → ξ u = 1

end Formalism.L2.Props
