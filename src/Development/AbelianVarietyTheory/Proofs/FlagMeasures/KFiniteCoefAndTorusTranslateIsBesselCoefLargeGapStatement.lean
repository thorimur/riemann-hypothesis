import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGap
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFiniteCoef_and_torusTranslate_isBesselCoef_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  first | exact @GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | exact GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | (intros; apply GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate <;> assumption)
