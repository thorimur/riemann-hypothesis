import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContractionStatement

noncomputable section

namespace PositivityTheory.SphericalProduct

theorem jacquet_hecke (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : A2 G :=
  GlobalTheory.T.jacquet_projection_hecke_holds G

theorem iwahori_u : IwahoriU :=
  GlobalTheory.T.iwahori_unipotent_datum

theorem dom_u : DomU :=
  GlobalTheory.T.dominant_unipotent_contraction

end PositivityTheory.SphericalProduct

end
