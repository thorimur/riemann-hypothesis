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
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
open scoped ModularForm MatrixGroups
namespace Formalism.ConjugateSelfDual
abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω

abbrev Qbar (l : ℕ) [Fact l.Prime] := PadicAlgCl l

def cyc (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    G F Ω →* (Qbar l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter (Ω) l).comp
      (MulSemiringAction.toRingAut (G F Ω) (Ω)))

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def IsPlaceOver (A : ValuationSubring (Ω)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : 𝓞 F, A.valuation (algebraMap F (Ω) (x : F)) < 1 ↔ x ∈ v.asIdeal

def normV (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

def Inertia (A : ValuationSubring (Ω)) : Set (G F Ω) :=
  {σ | σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1}

def IsFrob (A : ValuationSubring (Ω)) (q : ℕ) (σ : G F Ω) : Prop :=
  σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1

end places
end Formalism.ConjugateSelfDual
end
