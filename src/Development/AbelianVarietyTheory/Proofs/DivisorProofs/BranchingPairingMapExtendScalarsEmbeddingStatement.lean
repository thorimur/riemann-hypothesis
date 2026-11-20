import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingMapExtendScalarsEmbedding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingPairing_map_extendScalars_embedding : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1)
    (Λ : ι → DomWeight N) (σ : ι → DomWeight n) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) =
      GlobalTheory.BrPairF.brPairF σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ _ v) := by
  first | exact @GlobalTheory.BrPairF.brPairF_map_descent | exact GlobalTheory.BrPairF.brPairF_map_descent | (intros; apply GlobalTheory.BrPairF.brPairF_map_descent <;> assumption)
