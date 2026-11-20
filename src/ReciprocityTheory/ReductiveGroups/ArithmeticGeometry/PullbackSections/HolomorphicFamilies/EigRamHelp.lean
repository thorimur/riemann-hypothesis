import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

open Formalism.L2.Pj

section Induce

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]

end Induce

theorem vLa_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp0 : p ≠ 0)
    (hp : (p : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (p : K) := by
  have h1 : la.valuation K (algebraMap (𝓞 K) K (p : 𝓞 K)) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem la _).2 hp
  have h2 : la.valuation K (algebraMap (𝓞 K) K (p : 𝓞 K)) ≠ 0 := by
    rw [Ne, map_eq_zero, map_natCast]
    exact_mod_cast hp0
  have hlog := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at hlog
  unfold vLa
  rw [show ((p : K)) = algebraMap (𝓞 K) K (p : 𝓞 K) from (map_natCast _ _).symm]
  omega

section Host

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

end Host

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
