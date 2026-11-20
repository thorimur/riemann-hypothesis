import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj

open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace UpperTheory.GalN

theorem cusp_of_pair (hGK : GlobalTheory.Published.GelfandKazhdanDual) (hP : PairU) : CuspU := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
  exact hP E Ω l ι a ha π χ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩

theorem bridge' : GlobalTheory.Published.GelfandKazhdanDual → (CarU → CarU) ∧ (PairU → CuspU) :=
  fun hGK => ⟨id, cusp_of_pair hGK⟩

end UpperTheory.GalN
