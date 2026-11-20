import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConst
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : Bst P), (∀ g : ↥(GK K), actSt P (g : GQ l) x = x) ↔ ∃ c : ↥(K0 K), x = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
  first | exact @GlobalTheory.PMon.stInv_iff | exact GlobalTheory.PMon.stInv_iff | (intros; apply GlobalTheory.PMon.stInv_iff <;> assumption)
