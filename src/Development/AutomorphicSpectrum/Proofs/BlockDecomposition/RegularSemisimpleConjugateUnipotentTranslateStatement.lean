import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleConjugateUnipotentTranslate
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_semisimple_conjugate_unipotent_translate : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (δ : GF V), IsRegSS δ.1.1 → δ ∈ (frameFlag hC).parRat D.sp.cm → ∀ ν ∈ (frameFlag hC).unipRat D.sp.cm,
      ∃ g : GF V, g * δ * g⁻¹ = δ * ν := by
  first | exact @GlobalTheory.CompanionTheory.ParabConj.conj_translate | exact GlobalTheory.CompanionTheory.ParabConj.conj_translate | (intros; apply GlobalTheory.CompanionTheory.ParabConj.conj_translate <;> assumption)
