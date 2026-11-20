import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderSplitCoprimeConductor
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinSetSplitPlacesCoprimeConductor_twPl_under : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T), GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor | exact GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor | (intros; apply GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor <;> assumption)
