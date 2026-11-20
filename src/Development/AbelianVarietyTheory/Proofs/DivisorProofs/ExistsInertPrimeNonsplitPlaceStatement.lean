import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPrimeNonsplitPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inert_prime_nonsplit_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ Formalism.UG.IsInertAt F E v w := by
  first | exact @GlobalTheory.InertOfNoEmb.exists_isInertAt | exact GlobalTheory.InertOfNoEmb.exists_isInertAt | (intros; apply GlobalTheory.InertOfNoEmb.exists_isInertAt <;> assumption)
