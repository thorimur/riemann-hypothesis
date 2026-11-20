import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHoldsStatement
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.IsSmoothCharDpowM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequencesStatement

namespace GlobalTheory.RgGu.Leib.Hand

theorem leibnizOrd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    LeibnizOrd k :=
  GlobalTheory.T.leibniz_order_of_exact_sequences k (GlobalTheory.T.residue_sequence_holds k) (GlobalTheory.T.psi_gp_commutation_holds k) (GlobalTheory.T.phi_gp_commutation_holds k) (GlobalTheory.CompanionTheory.BZPsiPG.Hand.psiPG k) (GlobalTheory.CompanionTheory.BZPhiPG.phiPG k)
    (GlobalTheory.T.phi_pg_rank_zero_holds k)

end GlobalTheory.RgGu.Leib.Hand
