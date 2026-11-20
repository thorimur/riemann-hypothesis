import Development.AutomorphicSpectrum.Proofs.MetricProofs.CMFieldDegreeEqTwiceCard
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CM_field_degree_eq_twice_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card | exact GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card <;> assumption)
