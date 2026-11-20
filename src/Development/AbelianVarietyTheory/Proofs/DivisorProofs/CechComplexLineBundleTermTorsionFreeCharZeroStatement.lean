import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexLineBundleTermTorsionFreeCharZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComplexLineBundle_term_torsionFree_charZero : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) → ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 → ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  first | exact @GlobalTheory.CechPic.cechLB_X_noZSMulDivisors | exact GlobalTheory.CechPic.cechLB_X_noZSMulDivisors | (intros; apply GlobalTheory.CechPic.cechLB_X_noZSMulDivisors <;> assumption)
