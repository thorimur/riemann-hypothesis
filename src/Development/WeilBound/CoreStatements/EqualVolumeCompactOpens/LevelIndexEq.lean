import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SaOpen
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.ExistsDualBasis

namespace PositivityTheory.EqVol

theorem indexEq : IndexEq := indexEq_of (coSA saOpen) divisible

theorem levelIndexEq : LevelIndexEq :=
  levelIndexEq_of indexEq (levelCO hatCompactOpen) levelConj (levelRat hatRat)

end PositivityTheory.EqVol
