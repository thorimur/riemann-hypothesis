import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicVectorsTransitive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_isotropic_vectors_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E), (∀ e, σ (σ e) = e) → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 → z ≠ 0 → form σ J z z = 0 →
    ∃ g ∈ ratU σ J, ∃ μ : E, μ ≠ 0 ∧ mat g *ᵥ incV F z = incV F (μ • x) := by
  first | exact @GlobalTheory.MidLineWitt.exists_ratU_isotropic | exact GlobalTheory.MidLineWitt.exists_ratU_isotropic | (intros; apply GlobalTheory.MidLineWitt.exists_ratU_isotropic <;> assumption)
