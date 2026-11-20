import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  first | exact @GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one | exact GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one | (intros; apply GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one <;> assumption)
