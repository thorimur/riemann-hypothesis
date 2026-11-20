import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPointDeterminesPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

namespace GlobalTheory

theorem _root_.GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion :
    _root_.GlobalTheory.ThetaPtDeterminesSt ∧ _root_.GlobalTheory.EndDeterminedOnTorsionSt := by
  have hL := _root_.GlobalTheory.allSixLaws
  refine ⟨_root_.GlobalTheory.thetaPt_determines hL.1,
    _root_.GlobalTheory.endDeterminedOnTorsion hL.1 ?_⟩
  exact _root_.GlobalTheory.card_zeros_on_torsion_coset_le hL.1.mulN
    (fun K _ X _ p L hL => _root_.GlobalTheory.SectionRing.exists_sectionRing K X p L hL)
    (_root_.GlobalTheory.PowSec.exists_basis_sections hL.1.globalSectionsRank)
    (_root_.GlobalTheory.veryAmple_lbPow hL.1.ample)
    (_root_.GlobalTheory.exists_mulPull_sec hL.1.mulPull)
    (fun K _ X p g hp U hU hne => _root_.GlobalTheory.SmoothDim.ringKrullDim_affineOpen K X p g hp U hU hne)
    _root_.GlobalTheory.polAV_isIntegral_of_isAlgClosed
    (fun K T _ _ _ _ 𝒜 _ m x hx hne d s hs hpow => _root_.GlobalTheory.isIntegral_adjoin_of_mul_pow_mem K T 𝒜 m x hx hne d s hs hpow)
    _root_.GlobalTheory.graded_bezout_bound

end GlobalTheory
