import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightPrimeVanishing
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_height_prime_vanishing : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (hp : (resP v).Prime) (e : Ext v) (y : AlgPt (O.Φ.C c).Y) (Ch : Type)
    (inC : Ch → Prop) (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL)),
    resP v = p → PtData O c b n hp e y inC M → ∀ k : ℕ, k + 3 ≤ n → ∀ a, inC a → ∀ u u' : Fin (D.R.f * O.N) → AlgebraicClosure D.what₂.LL,
      supN e.w ((M a).mulVec u) ≤ 1 → supN e.w ((M a).mulVec u') ≤ 1 →
      e.w (dotProduct ((M a).mulVec u)
        (((dualForm O.S.Dw b).map (Int.castRingHom (AlgebraicClosure D.what₂.LL))).mulVec ((M a).mulVec u'))) ≤
        e.w (p : AlgebraicClosure D.what₂.LL) ^ k := by
  first | exact @GlobalTheory.EqHalf.IsoLevel.isotropic_dualForm | exact GlobalTheory.EqHalf.IsoLevel.isotropic_dualForm | (intros; apply GlobalTheory.EqHalf.IsoLevel.isotropic_dualForm <;> assumption)
