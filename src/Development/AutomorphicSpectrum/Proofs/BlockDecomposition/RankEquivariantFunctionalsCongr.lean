import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentLengthTwoReducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentLengthTwoIrreducibleSubStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueIrreducibleSubLengthTwoStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.StdSubTop

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem segmentRepresentation : GlobalTheory.Published.SegmentRepresentation :=
  GlobalTheory.T.unique_irreducible_sub_length_two (GlobalTheory.T.segment_length_two_irreducible_sub GlobalTheory.T.segment_length_two_reducible)

end GlobalTheory.CompanionTheory.StdSubTop

end
