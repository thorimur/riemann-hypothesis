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

open NumberField IsDedekindDomain

namespace HeckeCharacterZeroLocus.ThmBIn

variable {K : Type} [Field K] [NumberField K]

def Kmax (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : Set (GL (Fin n) (w.adicCompletion K)) :=
  {g | ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)) i j ∈ w.adicCompletionIntegers K ∧
    ((g⁻¹ : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)) i j ∈
      w.adicCompletionIntegers K}

def IsDiagAt (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ϖ : 𝓞 K) (d : List ℤ) (α : GL (Fin n) (w.adicCompletion K)) :
    Prop :=
  (α : Matrix (Fin n) (Fin n) (w.adicCompletion K)) =
    Matrix.diagonal (fun i => (algebraMap K (w.adicCompletion K) (ϖ : K)) ^ (d.getD i.1 0))

def IsCosetRep {G : Type} [Group G] (Kset : Set G) (α : G) (R : Finset G) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ Kset, ∃ k₂ ∈ Kset, γ = k₁ * α * k₂) ∧
    ∀ x : G, (∃ k₁ ∈ Kset, ∃ k₂ ∈ Kset, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Kset

def IsSphPD (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ϖ : 𝓞 K) (ω : GL (Fin n) (w.adicCompletion K) → ℂ) : Prop :=
  ω 1 = 1 ∧
  (∀ g, ∀ k ∈ Kmax w n, ω (g * k) = ω g ∧ ω (k * g) = ω g) ∧
  (∀ (m : ℕ) (g : Fin m → GL (Fin n) (w.adicCompletion K)) (z : Fin m → ℂ),
    (∑ i, ∑ j, star (z i) * z j * ω ((g i)⁻¹ * g j)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, star (z i) * z j * ω ((g i)⁻¹ * g j)).re) ∧
  ∀ (d : List ℤ) (α : GL (Fin n) (w.adicCompletion K)), IsDiagAt w ϖ d α →
    ∀ R, IsCosetRep (Kmax w n) α R → ∀ x, ∑ γ ∈ R, ω (x * γ) = (∑ γ ∈ R, ω γ) * ω x

def splitLab (n k : ℕ) : List ℤ := List.replicate (n - k) 0 ++ List.replicate k (-1)

def satPolyL (c : List ℤ → ℂ) (q : ℕ) (r : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (r + 1), Polynomial.monomial (r - k)
    ((-1 : ℂ) ^ k * ((q : ℝ) ^ (-((k * (r - k) : ℕ) : ℝ) / 2) : ℝ) * c (splitLab r k))

def SatakeBoundLocal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K), ϖ ∈ w.asIdeal →
    ϖ ∉ w.asIdeal ^ 2 → ∀ (n : ℕ) (ω : GL (Fin n) (w.adicCompletion K) → ℂ), IsSphPD w ϖ ω →
    ∀ c : List ℤ → ℂ, (∀ k ≤ n, ∀ α R, IsDiagAt w ϖ (splitLab n k) α → IsCosetRep (Kmax w n) α R →
      c (splitLab n k) = ∑ γ ∈ R, ω γ) →
    ∀ a : ℂ, (satPolyL c (Ideal.absNorm w.asIdeal) n).IsRoot a →
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-((n : ℝ) - 1) / 2) ≤ ‖a‖ ∧
        ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((n : ℝ) - 1) / 2)

end HeckeCharacterZeroLocus.ThmBIn

end
