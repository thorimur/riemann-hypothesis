import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerNonvanishing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_power_nonvanishing : ∀ {Y : Scheme.{0}} {D : LB Y} {J : Type} (s : J → LB.Sec D) (i : J) {x : Y}, x ∈ Out.nonzeroLocus (s i) → ∀ u : ℕ, ∃ σ : LB.Sec (pw D u), x ∈ Out.nonzeroLocus σ := by
  first | exact @GlobalTheory.PowSecNonzero.exists_pw_sec_nonzero | exact GlobalTheory.PowSecNonzero.exists_pw_sec_nonzero | (intros; apply GlobalTheory.PowSecNonzero.exists_pw_sec_nonzero <;> assumption)
