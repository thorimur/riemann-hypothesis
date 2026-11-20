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
import Mathlib.Order.CompletePartialOrder
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

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

variable {F : Type*} [Field F]

section Places

variable {L : Type*} [Field L] [Algebra F L]

def placesOver (S : Set (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}

theorem mem_placesOver {S : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOver S ↔ ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal :=
  Iff.rfl

end Places

variable {Ω : Type*} [Field Ω] [Algebra F Ω]

def IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) (E : IntermediateField F Ω) : Prop :=
  ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal

variable (F Ω) in

noncomputable def maxUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :
    IntermediateField F Ω :=
  ⨆ (E : IntermediateField F Ω) (_ : FiniteDimensional F E) (_ : IsUnramifiedOutside S E), E

variable (F Ω) in

abbrev galUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :=
  Gal(maxUnramifiedOutside F Ω S / F)

end GroundTheory.ProfCoh
