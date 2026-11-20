import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.DedekindDomain.Different
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem ramified_dvd_differentIdeal {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1) :
    w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have h2 : 2 ≤ w.asIdeal.ramificationIdx (𝓞 K) := by
    have := Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)
    omega
  set v := w.asIdeal.under (𝓞 K)
  have hv0 : v ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot
  have : v.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hv0
  have hmap : v.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).not.mpr hv0
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v w.asIdeal hmap
  have hdvd : w.asIdeal ^ w.asIdeal.ramificationIdx (𝓞 K) ∣
      v.map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [he]
    exact pow_multiplicity_dvd _ _
  have := pow_sub_one_dvd_differentIdeal_aux (𝓞 K) K L w.asIdeal (by omega) hv0 hdvd
  exact (dvd_pow_self _ (by omega)).trans this

variable (K L) in

theorem finite_setOf_ramified :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
  (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset
    fun _ hw => ramified_dvd_differentIdeal hw

end GroundTheory.ProfCoh
