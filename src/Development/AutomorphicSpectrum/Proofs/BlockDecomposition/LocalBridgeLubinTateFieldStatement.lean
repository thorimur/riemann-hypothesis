import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateField
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_bridge_lubin_tate_field : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | exact GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia <;> assumption)
