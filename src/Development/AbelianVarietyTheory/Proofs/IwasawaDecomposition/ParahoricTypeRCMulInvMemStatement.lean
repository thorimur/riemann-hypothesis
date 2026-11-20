import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMem
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricTypeRC_mul_inv_mem : ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) F), k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c → k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c := by
  first | exact @GlobalTheory.ParGroup.parJ_mul_inv | exact GlobalTheory.ParGroup.parJ_mul_inv | (intros; apply GlobalTheory.ParGroup.parJ_mul_inv <;> assumption)
