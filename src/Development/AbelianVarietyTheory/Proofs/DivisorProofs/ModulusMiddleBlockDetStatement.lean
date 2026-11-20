import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusMiddleBlockDet
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_middle_block_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (l d N : ℕ), l + d ≤ N → ∀ g : GL (Fin d) k,
    GlobalTheory.SmGL.deltaHalf k (fun j : Fin 3 => Fin (GlobalTheory.CuspBlock.tripSizes l d N j)) (GlobalTheory.CuspBlock.midHom k l d N g) =
      GlobalTheory.SmGL.detChar (Fin d) (GlobalTheory.SmGL.absPow k (((N : ℂ) - 2 * l - d) / 2)) g := by
  first | exact @GlobalTheory.CuspBlock.deltaHalf_midHom | exact GlobalTheory.CuspBlock.deltaHalf_midHom | (intros; apply GlobalTheory.CuspBlock.deltaHalf_midHom <;> assumption)
