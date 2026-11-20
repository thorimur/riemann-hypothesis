import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_nu_twisted_tuple_ramified_at_twist_place : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m), ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (GlobalTheory.FunObj.SqNum.nuH G t i j).UnrAt P := by
  first | exact @GlobalTheory.SqTop.nuH_not_unrAt_twPl | exact GlobalTheory.SqTop.nuH_not_unrAt_twPl | (intros; apply GlobalTheory.SqTop.nuH_not_unrAt_twPl <;> assumption)
