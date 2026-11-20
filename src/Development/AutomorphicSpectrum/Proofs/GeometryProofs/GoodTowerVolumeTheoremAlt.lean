import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TopAvoid
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsRightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GivenOfAllInputsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem good_tower_and_volume_final :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
    GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections →
    GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → GR.QuotientByFiniteFlatStatement → GR.ZarhinStatement →
    Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hAI hHS hBig hResK hSA hFHT hGaga hLine hQ hZ
  obtain ⟨hM, hKey, hSA', hSeg, hResK', _hSAst, hFHT', hGaga', _hSlope, hPB, hPHS, hPAn, hNine, _hAnti⟩ :=
    GlobalTheory.T.given_of_all_inputs hAI hHS hBig hResK hSA hFHT hGaga hLine
  exact GlobalTheory.T.final_theorem_of_inputs_right hM hKey hSA' hSeg hResK' hFHT' hGaga' hLine hPB hPHS hPAn hNine
    (GlobalTheory.T.points_integrable_of_resolution_statement hResK) GlobalTheory.CompanionTheory.Ar.Giv.topAvoid hQ hZ GlobalTheory.thetaUnifAV_closed

end GlobalTheory.CompanionTheory.Ar.Link
