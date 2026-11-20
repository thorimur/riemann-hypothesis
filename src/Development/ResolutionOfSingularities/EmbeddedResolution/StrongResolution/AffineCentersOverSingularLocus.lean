import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleOfPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothStrictTransformComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.PrincipalizationWithRadicalCenters
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem smooth_opens_ι {X : Scheme.{u}} (U : X.Opens) :
    AlgebraicGeometry.Smooth U.ι := by
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  exact (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso _) :
    (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth)

private theorem smooth_ι_comp_of_le_smoothLocus {X Z : Scheme.{u}} (f : X ⟶ Z)
    [AlgebraicGeometry.LocallyOfFinitePresentation f] (U : X.Opens)
    (hU : U ≤ AlgebraicGeometry.Scheme.Hom.smoothLocus f) :
    AlgebraicGeometry.Smooth (U.ι ≫ f) := by
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  have hx : (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.stalkMap f (U.ι x))).FormallySmooth := hU x.2
  have hg : (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth :=
    RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have heq : (CommRingCat.Hom.hom
        (AlgebraicGeometry.Scheme.Hom.stalkMap (U.ι ≫ f) x)).FormallySmooth =
      (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap f (U.ι x) ≫
        AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth :=
    congrArg (fun φ => (CommRingCat.Hom.hom φ).FormallySmooth)
      (AlgebraicGeometry.Scheme.Hom.stalkMap_comp U.ι f x)
  exact Eq.mpr heq (RingHom.FormallySmooth.comp hx hg)

private theorem mem_smoothLocusComplement_iff {X Z : Scheme.{u}} (f : X ⟶ Z)
    [AlgebraicGeometry.LocallyOfFinitePresentation f] (x : ↥X) :
    x ∈ (↑(smoothLocusComplement f) : Set ↥X) ↔
      x ∉ (↑(AlgebraicGeometry.Scheme.Hom.smoothLocus f) : Set ↥X) :=
  Iff.rfl

private theorem ker_morphismRestrict {X W : Scheme.{u}} (f : X ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion f] (V : W.Opens) :
    AlgebraicGeometry.Scheme.Hom.ker (f ∣_ V) =
      (AlgebraicGeometry.Scheme.Hom.ker f).comap V.ι :=
  OpenImmersionRestriction.ker_eq_comap_ker_of_isPullback_isOpenImmersion f V.ι (f ∣_ V) ((f ⁻¹ᵁ V).ι)
    (AlgebraicGeometry.isPullback_morphismRestrict f V).flip

private theorem inducedBlowupsWithoutIso_eq_withoutIsoBlowups {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY)
    (h : S.TransitionsAreBlowups) : S.inducedBlowupsWithoutIso h = (S.inducedBlowups h).withoutIsoBlowups := rfl

private noncomputable def restrictEmbeddingDatumBasicOpen {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u}) (r : Γ(D.ambient, ⊤)) :
    EmbeddingDatum k (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) where
  ambient := (D.ambient.basicOpen r).toScheme
  ambientStruct := (D.ambient.basicOpen r).ι ≫ D.ambientStruct
  emb := D.emb ∣_ D.ambient.basicOpen r
  isAffine_ambient := (AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r
  smooth_ambientStruct := by
    have := D.smooth_ambientStruct
    have := smooth_opens_ι (D.ambient.basicOpen r)
    infer_instance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := by
    have : AlgebraicGeometry.IsAffine (D.ambient.basicOpen r).toScheme :=
      (AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r
    exact inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := by
    rw [ker_morphismRestrict]
    exact D.nonzeroOnComponents_ker.comap_of_isOpenImmersion _
  comp_eq := by
    rw [← Category.assoc, AlgebraicGeometry.morphismRestrict_ι, Category.assoc, D.comp_eq]
  sncEmpty := by
    have := D.smooth_ambientStruct
    have := smooth_opens_ι (D.ambient.basicOpen r)
    exact hsnc k _ _ inferInstance

private theorem isPullbackSeq_of_smooth
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p'] [AlgebraicGeometry.QuasiCompact p']
    [AlgebraicGeometry.IsReduced Y'] [AlgebraicGeometry.IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) (hsmφ : AlgebraicGeometry.Smooth φ) (ψ : Y' ⟶ Y)
    (hφ : φ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ψ φ D.emb) :
    IsPullbackBlowupSequence ψ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have := hsmφ
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' φ ψ hφ hsq

private theorem centersLieOver_of_withoutIsoBlowups {X : Scheme.{u}} (s : SequenceOfBlowups X) (Z : Set ↥X)
    (h : s.withoutIsoBlowups.CentersLieOver Z) : s.CentersLieOver Z := by
  intro i hi x hx
  have hne : s.center i ≠ ⊤ := by
    intro h0
    have h1 : (s.center i).support = ⊥ :=
      (AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff _).mpr h0
    have h2 : x ∈ ((⊥ : TopologicalSpace.Closeds ↥(s.schemeAt i)) : Set ↥(s.schemeAt i)) := by
      rw [← h1]; exact hx
    exact h2
  obtain ⟨j, hj, hji⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top hi hne
  subst hji
  have h1 := h j (by rw [SequenceOfBlowups.withoutIsoBlowups_length]; exact hj) x
    (by rw [SequenceOfBlowups.withoutIsoBlowups_center]; exact hx)
  rwa [SequenceOfBlowups.withoutIsoBlowups_projectionToBase] at h1

private theorem blowupSequence_centersLieOver_congr {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] {S T : EmbeddedBlowupSequence k Y pY} (e : S = T)
    (hS : S.TransitionsAreBlowups) (hT : T.TransitionsAreBlowups) (Z : Set ↥Y)
    (h : (S.inducedBlowups hS).CentersLieOver Z) : (T.inducedBlowups hT).CentersLieOver Z := by
  subst e
  exact h

private theorem quasiCompact_of_embeddingDatum {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY) :
    AlgebraicGeometry.QuasiCompact pY := by
  rw [← D.comp_eq]
  infer_instance

theorem centerOffDetached_eq_top_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).centerOffDetached t = ⊤ := by
  have : AlgebraicGeometry.QuasiCompact pY := quasiCompact_of_embeddingDatum D
  have hiso := OpenImmersionRestriction.detachedLocusIsOpen_toEmbeddedBlowupSequence OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment hres hB hrad
    (OpenImmersionRestriction.chartIsolationHypotheses_reducedVanishingAssignment (canonicalPrincipalization hres hrad)) k Y pY D
  have hnoe : NoetherianSpace
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t) :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian _
      (EmbeddedBlowupSequence.isNoetherian_schemeAt (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad))) t
      (le_of_lt ht)
  have hopen : IsOpen ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t) :=
    hiso t ht
  apply (Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have h1 := EmbeddedBlowupSequence.support_centerOffDetached_subset_preimage
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t hy
  have h2 : y ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t :=
    OpenImmersionRestriction.mem_detachedLocus_of_mem_support_ambientCenter hres hB hrad D hsm t ht y h1
  have h3 := EmbeddedBlowupSequence.support_centerOffDetached_subset_detachedClosureCompl
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t hnoe hopen hy
  rw [EmbeddedBlowupSequence.detachedClosureCompl_coe, EmbeddedBlowupSequence.detachedClosure_coe] at h3
  exact h3 h2

theorem toEmbeddedBlowupSequence_center_eq_top_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).center t = ⊤ := by
  rw [EmbeddedBlowupSequence.inducedBlowups_center, EmbeddedBlowupSequence.totalCenter_eq,
    centerOffDetached_eq_top_of_smooth hres hB hrad D hsm t ht]
  exact AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty ..

private theorem withoutIsoBlowups_length_eq_zero_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).lengthWithoutIsoBlowups = 0 := by
  by_contra hne
  have h0 : 0 < ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).lengthWithoutIsoBlowups :=
    Nat.pos_of_ne_zero hne
  have h1 := SequenceOfBlowups.nontrivialIndex_lt_length _ h0
  have h2 := SequenceOfBlowups.center_nontrivialIndex_ne_top _ h0
  rw [EmbeddedBlowupSequence.inducedBlowups_length] at h1
  exact h2 (toEmbeddedBlowupSequence_center_eq_top_of_smooth hres hB hrad D hsm hbl _ h1)

private theorem centersLieOver_embeddedResolutionRuleOfPrincipalization
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hA : IsFunctorialPrincipalization (canonicalPrincipalization hres hrad))
    (hw : TransitionsAreBlowupsForEmbeddings (canonicalPrincipalization hres hrad))
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFinitePresentation pY]
    (D : EmbeddingDatum k Y pY) :
    (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  intro i hi x hx
  by_contra hns
  have hy : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
      (↑(AlgebraicGeometry.Scheme.Hom.smoothLocus pY) : Set ↥Y) := by
    by_contra h
    exact hns ((mem_smoothLocusComplement_iff pY _).mpr h)
  obtain ⟨W, hWopen, hW⟩ :=
    ((AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding D.emb).isInducing).isOpen_iff.mp
      (AlgebraicGeometry.Scheme.Hom.smoothLocus pY).isOpen
  have hWy :
      D.emb
        ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
        ∈ W := by
    have h2 :
        (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
          ⇑D.emb ⁻¹' W := by
      rw [hW]; exact hy
    exact h2
  obtain ⟨U', hU'mem, hxU', hU'le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_basicOpen D.ambient)
      (show D.emb
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
          ∈ (⟨W, hWopen⟩ : D.ambient.Opens) from hWy)
  obtain ⟨r, hr⟩ := hU'mem
  have hyV : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
      D.emb ⁻¹ᵁ D.ambient.basicOpen r := by
    have h3 :
        D.emb
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
          ∈ D.ambient.basicOpen r := by
      rw [hr]; exact hxU'
    exact h3
  have hVle : (D.emb ⁻¹ᵁ D.ambient.basicOpen r) ≤
      AlgebraicGeometry.Scheme.Hom.smoothLocus pY := by
    intro z hz
    have h3 : D.emb z ∈ D.ambient.basicOpen r := hz
    rw [hr] at h3
    have h5 : z ∈ ⇑D.emb ⁻¹' W := hU'le h3
    rw [hW] at h5
    exact h5
  have hVaff : AlgebraicGeometry.IsAffine (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme :=
    ((AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r).preimage D.emb
  have hsmV : AlgebraicGeometry.Smooth ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) :=
    smooth_ι_comp_of_le_smoothLocus pY _ hVle
  have hqcV : AlgebraicGeometry.QuasiCompact ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) :=
    inferInstance
  have hlen0 : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) (restrictEmbeddingDatumBasicOpen D hsnc r)).length = 0 := by
    rw [embeddedResolutionRuleOfPrincipalization_apply, inducedBlowupsWithoutIso_eq_withoutIsoBlowups, SequenceOfBlowups.withoutIsoBlowups_length]
    exact withoutIsoBlowups_length_eq_zero_of_smooth hres hB hrad (restrictEmbeddingDatumBasicOpen D hsnc r) hsmV _
  have hps := isPullbackSeq_of_smooth (canonicalPrincipalization hres hrad) hA hw k Y
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme pY
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) D (restrictEmbeddingDatumBasicOpen D hsnc r)
      (D.ambient.basicOpen r).ι (smooth_opens_ι (D.ambient.basicOpen r))
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι rfl
      (AlgebraicGeometry.isPullback_morphismRestrict D.emb (D.ambient.basicOpen r))
  obtain ⟨ρ, e, h1, h2, h3, h4, h5, h6, h7⟩ := hps
  have hmemrange :
      (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
        Set.range ⇑(D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact hyV
  obtain ⟨x', hx'eq⟩ := hmemrange
  obtain ⟨z, hz1, hz2⟩ :=
    AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι)
      (g := (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i)
      x' x hx'eq
  have hex : ∃ w, w ∈
      (((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center i).comap
        (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase
            i))).support := by
    refine ⟨z, ?_⟩
    have hmem : z ∈
        (↑((((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center
          i).comap (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
            ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase
              i))).support) : Set _) := by
      rw [FunctorialResolution.EmbeddedResolution.support_comap]
      show (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i)) z
          ∈ (↑((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center
                i).support : Set _)
      rw [hz2]
      exact hx
    exact hmem
  obtain ⟨j, hj, -⟩ := (h4 i hi).mp hex
  rw [hlen0] at hj
  exact absurd hj (Nat.not_lt_zero j)

theorem toEmbeddedBlowupSequence_centersLieOver_smoothLocusComplement
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hA : IsFunctorialPrincipalization (canonicalPrincipalization hres hrad))
    (hw : TransitionsAreBlowupsForEmbeddings (canonicalPrincipalization hres hrad))
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFinitePresentation pY]
    (D : EmbeddingDatum k Y pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  apply centersLieOver_of_withoutIsoBlowups
  have h := centersLieOver_embeddedResolutionRuleOfPrincipalization hres hB hrad hA hw hsnc D
  rw [embeddedResolutionRuleOfPrincipalization_apply] at h
  exact h

theorem affineCentersLieOverSingularLocus_principalizationWithRadicalCenters :
    AffineCentersLieOverSingularLocus.{u} principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters := by
  intro k _ _ Y pY _ _ _ _
  unfold FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.InducedCentersLieOverSingularLocus
  have hbl0 :
      ((affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
          k Y pY).toEmbeddedBlowupSequence principalizationWithRadicalCenters).TransitionsAreBlowups :=
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters k Y pY _
  have key := toEmbeddedBlowupSequence_centersLieOver_smoothLocusComplement strictTransformIsBlowupOfClosedSubscheme
    canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical
    (isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
      smoothSubschemeIdealIsRadical
      (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect))
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters nilIsStrictNormalCrossingsOfSmooth
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
      k Y pY) hbl0
  rw [← AffineSpacePrincipalizationData.embeddedInducedBlowups_eq]
  exact blowupSequence_centersLieOver_congr
    (affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth k Y pY) hbl0 _ _ key

end FunctorialResolution.EmbeddedResolution
