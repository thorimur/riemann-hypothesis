import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCurveFiniteFieldPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.ArDegIndep.TieOther

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_curve_finite_field_place : ∀ (F : Type) [Field F] [NumberField F] (X Z : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (i : Z ⟶ X) [IsIntegral Z]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)],
    ∃ v : HeightOneSpectrum (𝓞 F), ((ringChar κ : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∀ z : Z, (q (i z)).asIdeal = v.asIdeal := by
  first | exact @GlobalTheory.fibre_over_prime_of_finite_field_action | exact GlobalTheory.fibre_over_prime_of_finite_field_action | (intros; apply GlobalTheory.fibre_over_prime_of_finite_field_action <;> assumption)
