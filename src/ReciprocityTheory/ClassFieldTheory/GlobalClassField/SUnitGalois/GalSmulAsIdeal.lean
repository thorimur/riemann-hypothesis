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
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField.SUnit

abbrev sUnits (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  (S : Set (HeightOneSpectrum (𝓞 K))).unit K

def unitsToSUnits (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (𝓞 K)ˣ →* sUnits K S :=
  (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).codRestrict (sUnits K S) fun x v _ => by
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuation_of_unit_eq]
    rfl

def valS (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnits K S →* (S → Multiplicative ℤ) :=
  MonoidHom.pi fun v => (HeightOneSpectrum.valuationOfNeZero (K := K) v.1).comp (sUnits K S).subtype

open scoped Pointwise in

instance galSmul (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L] :
    MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ v :=
    { asIdeal := σ • v.asIdeal
      isPrime := Ideal.IsPrime.smul σ
      ne_bot := by
        rw [Ideal.pointwise_smul_def, ne_eq,
          Ideal.map_eq_bot_iff_of_injective (MulAction.injective σ)]
        exact v.ne_bot }
  one_smul v := HeightOneSpectrum.ext (one_smul _ v.asIdeal)
  mul_smul σ τ v := HeightOneSpectrum.ext (mul_smul σ τ v.asIdeal)

def galUnits {K L : Type*} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) : Lˣ →* Lˣ :=
  Units.map σ.toRingEquiv.toMonoidHom
