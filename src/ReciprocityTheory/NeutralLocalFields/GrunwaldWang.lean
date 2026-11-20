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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
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
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Sheaves.Init

open NumberField IsDedekindDomain

namespace Neutral.GrunwaldWang

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

def LiesAbove (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A.nonunits ↔ x ∈ v.asIdeal

def IsComplexConjugationAt (w : InfinitePlace K) (c : Ω ≃ₐ[K] Ω) : Prop :=
  ∃ j : Ω →+* ℂ, (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧ InfinitePlace.mk (j.comp (algebraMap K Ω)) = w

def Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (m : ℕ), 0 < m → ¬ 8 ∣ m →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (A : T → ValuationSubring Ω), (∀ v, LiesAbove (A v) v.1) →
    ∀ χ : ∀ v : T, (A v).decompositionSubgroup K →* Multiplicative (ZMod m), (∀ v, Continuous (χ v)) →
    ∀ (R : Finset (InfinitePlace K)) (c : R → (Ω ≃ₐ[K] Ω)), (∀ w, IsComplexConjugationAt w.1 (c w)) →
    ∀ ε : R → Multiplicative (ZMod m), (∀ w, ε w ^ 2 = 1) →
      ∃ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod m), Continuous ψ ∧
        (∀ v : T, ψ.comp ((A v).decompositionSubgroup K).subtype = χ v) ∧ ∀ w : R, ψ (c w) = ε w

def SolubleStatement : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (N : Subgroup (Ω ≃ₐ[F] Ω)), N.Normal → IsOpen (N : Set (Ω ≃ₐ[F] Ω)) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : S → ValuationSubring Ω), (∀ v, LiesAbove (A v) v.1) →
    ∀ U : ∀ v : S, Subgroup ((A v).decompositionSubgroup F), (∀ v, (U v).Normal) →
      (∀ v, IsOpen (U v : Set ((A v).decompositionSubgroup F))) →
    ∀ R : Set (InfinitePlace F), (∀ w ∈ R, w.IsReal) →
      ∃ (H : Subgroup (Ω ≃ₐ[F] Ω)) (_ : H.Normal), IsOpen (H : Set (Ω ≃ₐ[F] Ω)) ∧ Group.IsSolvable ((Ω ≃ₐ[F] Ω) ⧸ H) ∧ H ⊔ N = ⊤ ∧
        (∀ v : S, H.subgroupOf ((A v).decompositionSubgroup F) = U v) ∧
        ∀ w ∈ R, ∀ c : Ω ≃ₐ[F] Ω, IsComplexConjugationAt w c → c ∈ H

end Neutral.GrunwaldWang
