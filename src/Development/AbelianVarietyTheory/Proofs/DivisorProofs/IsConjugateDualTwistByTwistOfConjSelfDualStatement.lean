import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDual

open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConjugateDualTwistBy_twist_of_conjSelfDual : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ} {π : GlobalTheory.CuspRep.CuspSub E m}, π.IsCsd → ∀ χ : Formalism.L2.Host.HChar E, GlobalTheory.GalOfCusp.IsConjDualBy (π.twist χ) (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹) := by
  first | exact @GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar | exact GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar | (intros; apply GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar <;> assumption)
