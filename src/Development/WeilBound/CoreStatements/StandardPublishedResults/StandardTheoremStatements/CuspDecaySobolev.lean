import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay

namespace PositivityTheory.Stage1.PM

theorem cuspDecaySobolev : GlobalTheory.Published.CuspDecaySobolev :=
  GlobalTheory.Size.cuspDecaySobolev_of_bound GlobalTheory.CuspGeo.cuspDecayBound

theorem cuspBounded : GlobalTheory.Published.CuspBounded :=
  GlobalTheory.CuspDecay.cuspBounded_of_cuspRapidDecay (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound)

end PositivityTheory.Stage1.PM
