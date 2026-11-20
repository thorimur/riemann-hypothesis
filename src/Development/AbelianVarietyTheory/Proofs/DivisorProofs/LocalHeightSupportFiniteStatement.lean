import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightSupportFinite
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Classical GlobalTheory.HtAdd

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_height_support_finite : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y)
    (L : GlobalTheory.HermLB V.p) (k : ℕ), k ≠ 0 → V.Induces A L k → ∀ x : Y.X, IsClosed ({x} : Set Y.X) →
    (Function.support fun v : HeightOneSpectrum (𝓞 F) => if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0).Finite := by
  first | exact @GlobalTheory.Mean4O.CoverFinSupp.finite_support | exact GlobalTheory.Mean4O.CoverFinSupp.finite_support | (intros; apply GlobalTheory.Mean4O.CoverFinSupp.finite_support <;> assumption)
