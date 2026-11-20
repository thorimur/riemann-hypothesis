import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section
namespace GlobalTheory.HermCSA
open NumberField
open scoped TensorProduct

def IsUInv (F C : Type) [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C] (s : C →+ C) : Prop :=
  (∀ x y, s (x * y) = s y * s x) ∧ (∀ x, s (s x) = x) ∧
    ∀ a : F, s (algebraMap F C a) = algebraMap F C (IsCMField.complexConj F a)

def ext (C K : Type) [Ring C] [CommRing K] (s : C →+ C) : K ⊗[ℤ] C →ₗ[ℤ] K ⊗[ℤ] C :=
  LinearMap.lTensor K s.toIntLinearMap

def LandherrCSA : Prop :=
  ∀ (F C : Type) [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] (s : C →+ C), IsUInv F C s →
    ∀ A A' : C, IsUnit A → IsUnit A' → s A = A → s A' = A' →
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (g : (ℚ_[ℓ] ⊗[ℤ] C)ˣ) (ν : ℚ_[ℓ]), ν ≠ 0 ∧
      (1 : ℚ_[ℓ]) ⊗ₜ A' = ν • (ext C ℚ_[ℓ] s (g : ℚ_[ℓ] ⊗[ℤ] C) * ((1 : ℚ_[ℓ]) ⊗ₜ A) * (g : ℚ_[ℓ] ⊗[ℤ] C))) →
    (∃ g : (ℝ ⊗[ℤ] C)ˣ, (1 : ℝ) ⊗ₜ A' = ext C ℝ s (g : ℝ ⊗[ℤ] C) * ((1 : ℝ) ⊗ₜ A) * (g : ℝ ⊗[ℤ] C)) →
    ∃ (g : Cˣ) (c : F), IsCMField.complexConj F c = c ∧ (∀ τ : F →+* ℂ, 0 < (τ c).re) ∧
      A' = algebraMap F C c * (s (g : C) * A * g)

end GlobalTheory.HermCSA
