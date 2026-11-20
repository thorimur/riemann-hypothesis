import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCentralCharacterAtZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_central_character_at_zero : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd) (g : G2), thT n t M (dg2 z z * g) 0 = u0 n t M z * thT n t M g 0 := by
  first | exact @GlobalTheory.CompanionTheory.CenTheta.thT_zero_central | exact GlobalTheory.CompanionTheory.CenTheta.thT_zero_central | (intros; apply GlobalTheory.CompanionTheory.CenTheta.thT_zero_central <;> assumption)
