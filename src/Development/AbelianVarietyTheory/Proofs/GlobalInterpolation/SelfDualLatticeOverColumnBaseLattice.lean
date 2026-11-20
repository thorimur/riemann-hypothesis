import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat

namespace GlobalTheory.OverObj

theorem selfDualOverBase : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase :=
  GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice

end GlobalTheory.OverObj
