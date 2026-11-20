import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteField

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labels_semisimple_parameter_GL_finiteField : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r), ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  first | exact @GlobalTheory.ParamLabel.exists_labels | exact GlobalTheory.ParamLabel.exists_labels | (intros; apply GlobalTheory.ParamLabel.exists_labels <;> assumption)
