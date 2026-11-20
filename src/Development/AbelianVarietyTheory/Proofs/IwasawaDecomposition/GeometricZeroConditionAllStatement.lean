import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricZeroConditionAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_zero_condition_all : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR N S Γ) R1.DivisorConditionAtBundlePoints → RL.At (prmR N S Γ) RL.Row_tie → RL.At (prmR N S Γ) S0.GeometricWeakCompatibility := by
  first | exact @GlobalTheory.Fc.GeoZeroAt.row_geo0_at | exact GlobalTheory.Fc.GeoZeroAt.row_geo0_at | (intros; apply GlobalTheory.Fc.GeoZeroAt.row_geo0_at <;> assumption)
