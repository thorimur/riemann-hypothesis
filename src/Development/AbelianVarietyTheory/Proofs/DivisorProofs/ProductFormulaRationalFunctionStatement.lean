import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaRationalFunction
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Classical GlobalTheory.HtAdd

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_rational_function : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (x : Y.X), IsClosed ({x} : Set Y.X) →
    ∀ g : Y.Fn, UnitAt x g →
    (Function.support fun v : HeightOneSpectrum (𝓞 F) => if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (valAt y.1 g)) else 0).Finite ∧
    (∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x), Real.log ‖ratVal g z‖) +
      ∑ᶠ v : HeightOneSpectrum (𝓞 F), (if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (valAt y.1 g)) else 0) = 0 := by
  first | exact @GlobalTheory.HtAdd.ProdFormulaPts.main | exact GlobalTheory.HtAdd.ProdFormulaPts.main | (intros; apply GlobalTheory.HtAdd.ProdFormulaPts.main <;> assumption)
