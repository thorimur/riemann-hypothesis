import Development.AutomorphicSpectrum.Proofs.MetricProofs.LineOfLargeDegreeOfMoriwaki
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodTowerVolumeTheoremAlt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeepStROfVolume
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem deepStR_of_hodgeTate : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections → GR.QuotientByFiniteFlatStatement → GR.ZarhinStatement → Pub.NefRR → Plug.DeepStR := by
  intro hAIS hMHS hMB hResK hSA hFHT hGaga hQ hZ hNef
  have hLLD := GlobalTheory.CompanionTheory.Ar.Giv.lineOfLargeDegree_of_moriwaki hAIS hMHS hMB hResK
  have hG : Top.Given := GlobalTheory.CompanionTheory.Ar.Link.given_of_moriwaki hAIS hMHS hMB hResK hSA hFHT hGaga hLLD
  have hTC := GlobalTheory.CompanionTheory.Ar.Link.good_tower_and_volume_final hAIS hMHS hMB hResK hSA hFHT hGaga hLLD hQ hZ
  have hHS : Prov.HS := by
    unfold Top.Given at hG
    exact hG.2.2.2.2.2.2.2.2.2.2.1
  have hG6 : ReciprocityTheory.ChartRestriction.G.Geo.BirationalPullbackPushforwardFormula := by
    unfold Prov.HS at hHS
    exact hHS.2.2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Plug.deepStR_of_volume hNef hG hAIS hG6 hTC.1 hTC.2

end GlobalTheory.CompanionTheory.Ar.Plug
