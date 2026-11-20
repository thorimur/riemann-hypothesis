import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviElementExists
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_levi_element_exists : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) → (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) → ∃ m : GLoc D.sp.cm.sig V.gram v, m ∈ stabLoc D.sp.cm.sig V.gram L v ∧ (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram m).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * α.1 := by
  first | exact @GlobalTheory.LeviIntegral.exists_stabLoc_mul_frame_of_isGood | exact GlobalTheory.LeviIntegral.exists_stabLoc_mul_frame_of_isGood | (intros; apply GlobalTheory.LeviIntegral.exists_stabLoc_mul_frame_of_isGood <;> assumption)
