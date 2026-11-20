import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzFarOfExact
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_tate_of_fargues_exact : HT.FarguesExact → HT.FarguesHodgeTate := by
  first | exact @PositivityTheory.Xgn.farguesHodgeTate_of_farguesExact | exact PositivityTheory.Xgn.farguesHodgeTate_of_farguesExact
