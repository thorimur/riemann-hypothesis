import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroColumns_classSumForm_posDef : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), SpectralModel.ColsPos (I.cols l) := by
  first | exact @GlobalTheory.Mem.Df.cols_pos | exact GlobalTheory.Mem.Df.cols_pos | (intros; apply GlobalTheory.Mem.Df.cols_pos <;> assumption)
