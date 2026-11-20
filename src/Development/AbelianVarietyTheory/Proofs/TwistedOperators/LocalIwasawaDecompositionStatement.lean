import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalIwasawaDecomposition
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_iwasawa_decomposition : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ v (g : GLoc D.sp.cm.sig V.gram v), ∃ p ∈ PLoc Φ.flag0 v, ∃ k ∈ stabLoc D.sp.cm.sig V.gram L v, g = p * k := by
  first | exact @GlobalTheory.IwFinFlag.iwasawa_minPar_fin | exact GlobalTheory.IwFinFlag.iwasawa_minPar_fin | (intros; apply GlobalTheory.IwFinFlag.iwasawa_minPar_fin <;> assumption)
