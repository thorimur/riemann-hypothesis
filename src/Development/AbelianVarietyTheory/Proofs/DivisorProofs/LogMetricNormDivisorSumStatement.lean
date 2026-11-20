import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricNormDivisorSum
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Classical GlobalTheory.HtAdd

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_metric_norm_divisor_sum : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) {ι : Type} (s : Finset ι) (a : ι → Sym D.host.E)
    (n : ι → ℤ), (∀ i ∈ s, (a i).2.1 = none) → ∀ (x : (O.var c).X) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ),
    under z = x →
    Real.log ((cxSt D.what₂.LL).pn (O.var c) σ _ ((adlOf (O.Φ.C c) (O.met.hm c) (∑ i ∈ s, Finsupp.single (a i) (n i))).m σ)
        ((cxSt D.what₂.LL).cx (O.var c) σ
          ((eqn (adlOf (O.Φ.C c) (O.met.hm c) (∑ i ∈ s, Finsupp.single (a i) (n i))).D x)⁻¹ : (O.var c).Fnˣ)) z) / 2 =
      ∑ i ∈ s, (n i : ℝ) * (Real.log ((cxSt D.what₂.LL).pn (O.var c) σ _
          ((adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (a i) 1)).m σ)
          ((cxSt D.what₂.LL).cx (O.var c) σ
            ((eqn (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (a i) 1)).D x)⁻¹ : (O.var c).Fnˣ)) z) / 2) +
        Real.log ‖ratVal (eqnRatio (O.Φ.C c) s a n x : (O.var c).Fn) z‖ := by
  first | exact @GlobalTheory.HtAddCx.log_pn_comb | exact GlobalTheory.HtAddCx.log_pn_comb | (intros; apply GlobalTheory.HtAddCx.log_pn_comb <;> assumption)
