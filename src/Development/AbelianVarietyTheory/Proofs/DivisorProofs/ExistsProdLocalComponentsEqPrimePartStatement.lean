import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePart

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prod_localComponents_eq_primePart : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (q : ℕ), q.Prime → ∀ g : Formalism.L2.Theta.GA D V, ∃ l : List (Formalism.L2.Theta.GA D V), (∀ h ∈ l, ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal ∧ GlobalTheory.WeilParts.SuppPl ε V h) ∧ GlobalTheory.BotClassDict.finStd V hG l.prod = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) (GlobalTheory.BotClassDict.finStd V hG g) := by
  first | exact @GlobalTheory.PrimePart.exists_prod_eq_part | exact GlobalTheory.PrimePart.exists_prod_eq_part | (intros; apply GlobalTheory.PrimePart.exists_prod_eq_part <;> assumption)
