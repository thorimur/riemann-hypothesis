import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_and_residualTriv_complexConj : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), Continuous (GlobalTheory.TwistDet.cConj X) ∧ ∀ (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g : GE N, ResTriv i s g → ResTriv i s (GlobalTheory.TwistDet.cConj X g) := by
  first | exact @GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv | exact GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv | (intros; apply GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv <;> assumption)
