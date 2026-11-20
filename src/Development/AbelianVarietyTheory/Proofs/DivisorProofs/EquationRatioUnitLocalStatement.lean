import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquationRatioUnitLocal
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Classical GlobalTheory.HtAdd

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equation_ratio_unit_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {ι : Type} (s : Finset ι) (a : ι → Sym E)
    (n : ι → ℤ) (x : Y.Y.X), UnitAt x (eqnRatio Y s a n x : Y.Y.Fn) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y), below y.1 = x →
      lgOf Y (∑ i ∈ s, Finsupp.single (a i) (n i)) v ε y =
        ∑ i ∈ s, (n i : ℝ) * lgOf Y (Finsupp.single (a i) 1) v ε y +
          Real.log (ε.w (valAt y.1 (eqnRatio Y s a n x : Y.Y.Fn))) := by
  first | exact @GlobalTheory.HtAdd.SumLines.lgOf_sum_single | exact GlobalTheory.HtAdd.SumLines.lgOf_sum_single | (intros; apply GlobalTheory.HtAdd.SumLines.lgOf_sum_single <;> assumption)
