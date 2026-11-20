import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenominatorAvoidingGivenPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_avoiding_given_primes : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (G : HeightOneSpectrum (𝓞 E) → Prop) (c : ℕ), 0 < c → ∀ x : Formalism.L2.Col.HomE E a b, (c : E) • x ∈ M → (∀ Q : HeightOneSpectrum (𝓞 E), ¬ G Q → x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M) → ∃ d : 𝓞 E, d ≠ 0 ∧ (d : E) • x ∈ M ∧ ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q := by
  first | exact @GlobalTheory.OffDen.exists_den_avoid | exact GlobalTheory.OffDen.exists_den_avoid | (intros; apply GlobalTheory.OffDen.exists_den_avoid <;> assumption)
