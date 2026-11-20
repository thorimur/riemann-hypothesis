import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingProjection
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_projection : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : GAd D.sp.cm.sig V.gram), t ∈ Φ.levi D.sp.cm (AF D.host.F) P → embAt D.sp.cm.sig V.gram S (projAt D.sp.cm.sig V.gram S t) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  first | exact @GlobalTheory.LeviAt.embAt_projAt_mem_levi | exact GlobalTheory.LeviAt.embAt_projAt_mem_levi | (intros; apply GlobalTheory.LeviAt.embAt_projAt_mem_levi <;> assumption)
