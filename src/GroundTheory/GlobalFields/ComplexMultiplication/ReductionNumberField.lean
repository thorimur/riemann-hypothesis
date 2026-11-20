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

namespace GroundTheory.Global

noncomputable section

open IsLocalRing NumberField IsDedekindDomain GroundTheory.Arith.Abelian

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev reductionLocalRing : Type _ := Localization.AtPrime v.asIdeal

instance reductionLocalRing.isDiscreteValuationRing :
    IsDiscreteValuationRing (reductionLocalRing v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot _

theorem reductionLocalRing.primeCompl_le : v.asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 K) := by
  intro a ha
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact fun h => ha (h.symm ▸ v.asIdeal.zero_mem)

instance reductionLocalRing.algebra : Algebra (reductionLocalRing v) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ v.asIdeal.primeCompl (nonZeroDivisors (𝓞 K))
    (reductionLocalRing.primeCompl_le v)

instance reductionLocalRing.isScalarTower : IsScalarTower (𝓞 K) (reductionLocalRing v) K :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _
    (reductionLocalRing.primeCompl_le v)

instance reductionLocalRing.isFractionRing : IsFractionRing (reductionLocalRing v) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl _ K

variable (W W' : WeierstrassCurve (reductionLocalRing v)) [W.IsElliptic] [W'.IsElliptic]

end

end GroundTheory.Global
