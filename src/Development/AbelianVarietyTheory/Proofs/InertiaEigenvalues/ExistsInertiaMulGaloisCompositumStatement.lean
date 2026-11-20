import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaMulGaloisCompositum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_mul_galois_compositum : ∀ (l : ℕ) [Fact l.Prime] (K' F K'' : FinExt l), (GK K').Normal → K''.1 = K'.1 ⊔ F.1 → ∀ h : GQ l, h ∈ GK F → (∀ x ∈ K0 K'', h x = x) → ∃ i : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)), i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (i : GQ l) ∈ GK F ∧ (i : GQ l)⁻¹ * h ∈ GK K'' := by
  first | exact @GlobalTheory.InertiaLift.lift | exact GlobalTheory.InertiaLift.lift | (intros; apply GlobalTheory.InertiaLift.lift <;> assumption)
