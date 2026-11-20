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

open NumberField IsDedekindDomain Polynomial Filter

namespace Formalism.L2

abbrev Fld : Type := IntermediateField ℚ (AlgebraicClosure ℚ)

def mapPl {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) :
    HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.comap ((RingOfIntegers.mapRingEquiv j).symm : 𝓞 L →+* 𝓞 F)
    (RingOfIntegers.mapRingEquiv j).symm.surjective v

theorem mem_mapPl {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    RingOfIntegers.mapRingEquiv j x ∈ (mapPl j v).asIdeal ↔ x ∈ v.asIdeal := by
  show (RingOfIntegers.mapRingEquiv j).symm (RingOfIntegers.mapRingEquiv j x) ∈ v.asIdeal ↔ _
  rw [RingEquiv.symm_apply_apply]

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

variable {F n}

namespace PreObj

end PreObj

variable (F n)

variable {F n}

namespace RARep

end RARep

variable (F n)

variable {F n}

variable (F n)

variable {F n}

end Formalism.L2
