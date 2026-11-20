import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFlagLastInclIsIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_flag_last_incl_isIso : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι), IsIso (GlobalTheory.FlagZ.Univ.incl ι N τ (Fin.last N)) := by
  first | exact @GlobalTheory.FlagZ.Univ.isIso_incl_last_step | exact GlobalTheory.FlagZ.Univ.isIso_incl_last_step | (intros; apply GlobalTheory.FlagZ.Univ.isIso_incl_last_step <;> assumption)
