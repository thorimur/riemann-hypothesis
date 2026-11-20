import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitSupportedFinitePartIntegralInert

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonSplitSupported_finitePart_integral_inert : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), GlobalTheory.WeilParts.NonSplitAt D v ε → ∀ g : Formalism.L2.Theta.GA D V, GlobalTheory.WeilParts.SuppPl ε V g → (∀ y : Fin V.rank → TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔ (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.InertLocalPoint.suppInert_and_intG | exact GlobalTheory.InertLocalPoint.suppInert_and_intG | (intros; apply GlobalTheory.InertLocalPoint.suppInert_and_intG <;> assumption)
