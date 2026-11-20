import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaKOfPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoHostVanE
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.HV.U

theorem pt (hN : LitN) : GlobalTheory.Published.PoitouTateDuality := GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hN.coh.pt

theorem lemmaK (hN : LitN) (hK : K.KBridge) : ∃ CK : ℝ, LemmaK CK :=
  (K.lemmaK (pt hN) hN.coh.lfK hN.coh.ltK hK).imp fun _ h => h.2

theorem localGaloisCohomology₂ (hN : LitN) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩

theorem hostVanE (hN : LitN) (hK : K.KBridge) : UnitaryThreeInertia.HostVanE := by
  obtain ⟨CK, hL⟩ := lemmaK hN hK
  exact X.So.hostVanE CK hL (pt hN) hN.coh.lfK hN.coh.ltK hN.coh.lf hN.coh.lt hN.coh.le

end UpperTheory.V.HV.U
