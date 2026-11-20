import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModule
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule : ∀ (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ), GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  first | (exact @GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (exact GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (intros; apply GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule  <;> assumption)
