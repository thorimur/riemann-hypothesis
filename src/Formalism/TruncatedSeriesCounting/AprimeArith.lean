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

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

def Mpar (ℓ g h : ℕ) : ℕ := (h + 2 * g) / (ℓ - 1) + 1

def sigE (ℓ g h j : ℕ) : ℕ :=
  ⌈((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1⌉₊

def a0E (ℓ g h j ell : ℕ) (rr : ℝ) : ℝ := 2 * (sigE ℓ g h j : ℝ) + rr + 2 * g * ell

def eE (ℓ g h j ell : ℕ) (rr kap : ℝ) : ℝ :=
  2 * rr + 4 * (sigE ℓ g h j : ℝ) + 2 * a0E ℓ g h j ell rr + 2 * kap

def MparGt : Prop :=
  ∀ ℓ g h : ℕ, 2 ≤ ℓ → h + 2 * g < (ℓ - 1) * Mpar ℓ g h

def SigELe : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ g h j : ℕ, 1 ≤ j →
    (sigE ℓ g h j : ℝ) ≤ 3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4

def EShape : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ (G g h j ell : ℕ) (C₀ rr kap : ℝ), 1 ≤ j → G ≤ g → 1 ≤ g → g ≤ h →
    1 ≤ ell → 0 ≤ C₀ →
    rr ≤ C₀ * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1) →
    kap ≤ C₀ * ((g : ℝ) * ell + Real.logb ℓ h + 1) →
    eE ℓ g h j ell rr kap ≤
      (12 * C₀ + 50) * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + (g : ℝ) * ell + Real.logb ℓ h)

def RrBound : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ (n : ℕ) [NeZero n] (H : ZMod n → ℕ) (G h j : ℕ) (cut : ZMod n) (s r : ℝ),
    1 ≤ h → (∀ x, H x ≤ 2 * h) → (∀ k : ℕ, 1 ≤ k → k ≤ j → H (cut + k) ≤ 2 * G) →
    s ≤ ∑' a : ℕ, ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ) +
        (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a →
    r ≤ s * ℓ / ((ℓ : ℝ) - 1) ^ 2 + (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) →
    r ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1)

def ExponentBoundOfRankAndKappaBounds : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ (G g h j ell : ℕ) (rr kap : ℝ), 1 ≤ j → G ≤ g → 1 ≤ g → g ≤ h → 1 ≤ ell →
    rr ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1) →
    kap ≤ ell + 20 * g * (1 + ell) + 5 * (4 * g / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * h)) →
    eE ℓ g h j ell rr kap ≤
      800 * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + (g : ℝ) * ell + Real.logb ℓ h)

def AprimeArith : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 11 ≤ ℓ → ∀ (b w S η j ell b₀ b₁ : ℕ) (rr : ℝ),
    1 ≤ j → C * ((j : ℝ) + 1) * ((w + S + η : ℕ) + 1 : ℝ) ≤ b → ell ≤ 3 * j + 1 →
    b ≤ b₀ → b₀ ≤ b + η → b ≤ b₁ → b₁ ≤ b + η →
    rr ≤ 20 * (((w + S + η : ℕ) : ℝ) / ℓ + ((b + η + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) +
      Real.logb ℓ (b + η + S : ℕ) + 1) →
    max (w + S + η) 1 < b₀ ∧ max (w + S + η) 1 < b₁ ∧ (b₀ : ℝ) < ℓ * b₁ ∧ (b₀ : ℝ) ≤ ℓ * b₁ / 2 ∧
      a0E ℓ (max (w + S + η) 1) (b + η + S) j ell rr < (b₁ : ℝ) / 2

def DDSat : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (P : Ideal (PowerSeries O)) (a : ℕ) (x : O),
      PowerSeries.C x ∈ Ideal.span {PowerSeries.C (ϖ ^ a)} ⊔ P →
      ϖ ^ a ∣ x ∨ PowerSeries.C x ∈ P

end Formalism.TruncatedSeriesCounting.WachCoordinates
