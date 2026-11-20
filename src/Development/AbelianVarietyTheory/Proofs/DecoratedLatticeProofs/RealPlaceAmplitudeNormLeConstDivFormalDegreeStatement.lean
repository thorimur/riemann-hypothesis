import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealPlaceAmplitudeNormLeConstDivFormalDegree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceAmplitude_norm_le_const_div_formalDegree : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 := by
  first | exact @GlobalTheory.AmpRec.exists_threshold_adm9_of_ties | exact GlobalTheory.AmpRec.exists_threshold_adm9_of_ties | (intros; apply GlobalTheory.AmpRec.exists_threshold_adm9_of_ties <;> assumption)
