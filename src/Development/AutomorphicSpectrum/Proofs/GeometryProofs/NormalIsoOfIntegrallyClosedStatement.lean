import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosed
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_iso_of_integrally_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ), NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) → IsoAt ξ' f (RingHom.id Ω) p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed | exact GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed | (intros; apply GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed <;> assumption)
