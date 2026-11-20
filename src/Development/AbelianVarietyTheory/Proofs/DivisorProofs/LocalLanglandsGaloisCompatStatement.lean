import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompat
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_galois_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
      (rc : GlobalTheory.LocGL.IrrGL (w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    ∀ t : ℝ, GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw t →
    ∀ g : G E Ω, IsFrob (F := E) B (normV w) g →
      (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
        Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ)))).prod := by
  first | exact @GlobalTheory.GeomFrobChar.charpoly_geomFrob | exact GlobalTheory.GeomFrobChar.charpoly_geomFrob | (intros; apply GlobalTheory.GeomFrobChar.charpoly_geomFrob <;> assumption)
