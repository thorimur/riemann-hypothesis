import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelHyperbolicBasisScaled
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_hyperbolicBasis_scaled : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (a : Fin D.R.rS),
    GlobalTheory.TypeAsm.phiV C τ (X.eX a) =
                 (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) ∧
    GlobalTheory.TypeAsm.phiV C τ (X.fY a) =
                 ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  first | exact @GlobalTheory.TypeAsm.FramePf.phiV_frame | exact GlobalTheory.TypeAsm.FramePf.phiV_frame | (intros; apply GlobalTheory.TypeAsm.FramePf.phiV_frame <;> assumption)
