import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedConjugatePlaceInverseUniformizerValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), ResEta D χ 0 → ∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w ≠ w' → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w' ∧ GlobalTheory.LFun.val (F := D.host.F) χ w' = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  first | exact @GlobalTheory.SplitUnr.unrAt_and_val_inv | exact GlobalTheory.SplitUnr.unrAt_and_val_inv | (intros; apply GlobalTheory.SplitUnr.unrAt_and_val_inv <;> assumption)
