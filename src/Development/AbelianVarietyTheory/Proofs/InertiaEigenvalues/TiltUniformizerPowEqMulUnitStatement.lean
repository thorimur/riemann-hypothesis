import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  first | (exact @GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (exact GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (intros; apply GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit  <;> assumption)
