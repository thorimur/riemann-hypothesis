import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_epsilon_factor_dependence_on_s : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ), finEps χ a s = finEps χ a (1 / 2) * (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift | exact GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift <;> assumption)
