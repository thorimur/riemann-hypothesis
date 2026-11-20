import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvr
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qVal_pullback_mul_ramification_complete_dvr : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D') (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' → Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  first | exact @GlobalTheory.QValPull.main | exact GlobalTheory.QValPull.main | (intros; apply GlobalTheory.QValPull.main <;> assumption)
