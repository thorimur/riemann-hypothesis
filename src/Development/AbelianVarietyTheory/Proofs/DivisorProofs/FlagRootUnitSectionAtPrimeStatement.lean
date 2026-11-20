import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRootUnitSectionAtPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.ArDegIndep.TieOther

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_root_unit_section_at_prime : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (B : ℝ), 2 ≤ B → ∀ (c : O.s.Comp) (τ : D.what₂.Tau) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ), p.Prime →
    ((p : 𝓞 D.what₂.LL) ∈ v.asIdeal) → p ∈ GlobalTheory.FlagAr.setB O.Y B →
    ∃ σ : (O.var c).Fn, (∀ y : (O.var c).X, UnitAt y ((∏ x : D.what₂.Tau × Fin O.N,
        if x.1 = τ then genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).D y else 1) / σ)) ∧
      ∃ C : ℝ, ∀ (e : Ext v) (y : AlgPt (O.var c)),
        (∑ x : D.what₂.Tau × Fin O.N, if x.1 = τ then (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).lg v e y else 0) -
          Real.log (e.w (valAt y.1 ((∏ x : D.what₂.Tau × Fin O.N,
            if x.1 = τ then genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).D (below y.1) else 1) / σ))) = C := by
  first | exact @GlobalTheory.HTConstRoot.exists_gen_const | exact GlobalTheory.HTConstRoot.exists_gen_const | (intros; apply GlobalTheory.HTConstRoot.exists_gen_const <;> assumption)
