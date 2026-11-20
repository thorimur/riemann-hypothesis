import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverPieces
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderBoundAlongSequence
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OrderReduction

def ValidPullbackAlongSmooth : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q],
      h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible

theorem validPullbackAlongSmooth_iff :
    ValidPullbackAlongSmooth.{u} ↔
      ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
        (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q],
        h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible :=
  Iff.rfl

end OrderReduction

namespace MaxContactCoverData

private theorem support_pow_subset {X : Scheme.{u}} (I : X.IdealSheafData) (s : ℕ) :
    ((I ^ s).support : Set ↥X) ⊆ (I.support : Set ↥X) := by
  intro x hx
  simp only [SetLike.mem_coe] at hx ⊢
  rw [mem_support_iff_stalkIdeal_ne_top] at hx ⊢
  intro hI
  apply hx
  rw [stalkIdeal_pow, hI, Ideal.top_pow]

private theorem prod_map_range_pow_ite_eq_pow {X : Scheme.{u}} (A : ℕ → X.IdealSheafData) (n s : ℕ) :
    (List.map (fun j => A j ^ (if j = n then s else 0)) (List.range (n + 1))).prod = A n ^ s := by
  have h1 : (List.map (fun j => A j ^ (if j = n then s else 0)) (List.range n)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [if_neg (Nat.ne_of_lt hj), pow_zero]
  rw [List.range_succ, List.map_append, List.prod_append, h1, one_mul]
  simp

private theorem exists_le_and_pow_le_tunedSheaf (k : Type u) [Field k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (I : X.IdealSheafData) (m s : ℕ) (hm : 1 ≤ m) :
    ∃ J : X.IdealSheafData, I ≤ J ∧ J ^ s ≤ tunedSheaf k p I m s := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨derivIdealSheafIterate k p n I, le_derivIdealSheafIterate k p n I, ?_⟩
  have h0 : (∑ j ∈ Finset.range (n + 1), (n + 1 - j) * (if j = n then s else 0))
      = (n + 1 - n) * (if n = n then s else 0) := by
    refine Finset.sum_eq_single n (fun b _ hb => by simp [hb]) (fun h => ?_)
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  have hsum : (∑ j ∈ Finset.range (n + 1), (n + 1 - j) * (if j = n then s else 0)) = s := by
    rw [h0, if_pos rfl, Nat.add_sub_cancel_left, one_mul]
  have h := prod_pow_derivIdealSheafIterate_le_tunedSheaf k p I (n + 1) s
    (fun j => if j = n then s else 0) hsum.ge
  rw [prod_map_range_pow_ite_eq_pow] at h
  exact h

theorem balancedTunedIdeal_eq_balancedTunedSheaf (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] :
    balancedTunedIdeal T hv = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf T.base T.structMap T.ideal T.mult :=
  rfl

theorem nonzeroOnComponents_balancedTunedIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    NonzeroOnComponents (balancedTunedIdeal T hv) := by
  have := hv.locallyOfFiniteType
  obtain ⟨J, hIJ, hJ⟩ :=
    exists_le_and_pow_le_tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) hv.one_le_mult
  have hle : J ^ tuningExponent T.mult ≤ balancedTunedIdeal T hv := by
    rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
    exact hJ
  have hnz := hv.nonzeroOnComponents
  rw [nonzeroOnComponents_iff] at hnz ⊢
  intro C hC hsub
  refine hnz C hC ?_
  intro x hx
  have h1 := hsub hx
  have h2 := SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hle) h1
  have h3 := support_pow_subset J (tuningExponent T.mult) h2
  exact SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hIJ) h3

theorem orderAt_balancedTunedIdeal_le_tunedMult (htf : TunedSheafProperties.{u}) (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (x : ↥T.scheme) :
    orderAt (balancedTunedIdeal T hv) x ≤ ((tunedMult T : ℕ) : ℕ∞) := by
  have := hv.locallyOfFiniteType
  have := hv.charZero
  have := hv.smooth
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have htop : balancedTunedIdeal T hv = ⊤ := by
      rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv]
      exact balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty T.base T.structMap T.ideal hv.one_le_mult hemp
    rw [htop, orderAt_top]
    simp
  · have hmax : MaxOrderEq T.ideal T.mult :=
      ⟨(orderLE_iff T.ideal T.mult).2 hord, Set.nonempty_iff_ne_empty.2 hemp⟩
    have hLE := htf.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap
      T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)
    rw [orderLE_iff] at hLE
    have h2 : balancedTunedIdeal T hv = tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) := by
      rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
    rw [h2]
    exact hLE x

theorem isAdmissible_coverTriple_of_validPullbackAlongSmooth (hpb : OrderReduction.ValidPullbackAlongSmooth.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T)) :
    (coverTriple T hv).IsAdmissible := by
  have hvt := MaxContactOpenCover.isAdmissible_tunedTriple T hv (nonzeroOnComponents_balancedTunedIdeal T hv)
  have hqc := MaxContactOpenCover.quasiCompact_coverMap_comp_structureMorphism T hv hgood
  rw [MaxContactOpenCover.coverTriple_eq_tunedTriple_pullbackAlong T hv]
  exact @hpb (MaxContactOpenCover.tunedTriple T hv) hvt (chosenCoverData T hv).disjointUnion
    (coverMap T hv ≫ T.structMap) (coverMap T hv) (MaxContactCoverData.instSmoothCoverMap T hv) hqc rfl

theorem isSmoothDivisor_coverMaxContactIdeal (_hpb : OrderReduction.ValidPullbackAlongSmooth.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T)) :
    IsSmoothDivisor (coverTriple T hv).structMap (coverMaxContactIdeal T hv) := by
  refine FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal (coverMaxContactIdeal T hv) ?_
  intro x
  obtain ⟨U, hxU, m, c, a, _hinj, hnone, hsome⟩ :=
    (MaxContactCoverGeometry.inStrictNormalCrossingPositionAt_of_isMaxContactCover T hv hgood x).exists_etaleChart
  refine ⟨U, hxU, m, c, ?_⟩
  rcases ha : a 0 with _ | t
  · exact Or.inl (hnone 0 (by simp) ha)
  · exact Or.inr ⟨t, hsome 0 (by simp) t ha⟩

end MaxContactCoverData

namespace OrderReduction

theorem maxContactCoverProperties_of_tunedSheafProperties (htf : TunedSheafProperties.{u}) (hdim : DimensionNonincreasingAlongBlowups.{u})
    (hpb : ValidPullbackAlongSmooth.{u}) : MaxContactCoverProperties.{u} := by
  refine
    { strictTransform_admissible := ?_
      coSupport_le_preimage := ?_
      schemeDim_level_le := ?_
      exists_goodCover := ?_
      hasSNCWith_cons := ?_
      valid_level := ?_
      orderAt_level_le := ?_
      coverTriple_dim_le := ?_
      coverTriple_valid := ?_
      coverContact_admissible := ?_
      coverContact_snc := ?_
      tuning := htf }
  · intro k _ _ P P₁ p _ _ _ π _ Z E hZ hπ A A₁ μ hμ hordA hsupp htr H hH
    exact FunctorialResolution.EmbeddedResolution.isMaxContactHypersurface_strictTransform_of_orderAt_le k p π Z E hZ hπ A A₁ μ hμ hordA
      hsupp htr H hH
  · intro X X₁ π Z hπ A A₁ μ htr hsupp
    exact FunctorialResolution.EmbeddedResolution.OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf π Z hπ A A₁ μ htr hsupp
  · intro T hT s i hi
    exact hdim T hT s i hi
  · intro T hv hord
    exact MaxContactOpenCover.exists_isMaxContactCover T hv (MaxContactCoverData.orderAt_balancedTunedIdeal_le_tunedMult htf T hv hord)
  · intro k _ P p _ Z H N _hsmZ hsnc hZN hHZ
    exact FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_cons_of_le p Z H N hsnc hZN hHZ
  · intro T hT s i hi
    exact MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hT s i hi
  · intro T hT hord s i hi x
    exact FunctorialResolution.EmbeddedResolution.orderAt_ideal_le_mult_along_sequence T hT hord s i hi x
  · intro T hv
    exact MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim T hv
  · intro T hv _hord hgood
    exact MaxContactCoverData.isAdmissible_coverTriple_of_validPullbackAlongSmooth hpb T hv hgood
  · intro T hv hgood _
    exact MaxContactCoverGeometry.isMaxContactHypersurface_coverMaxContactIdeal T hv hgood
  · intro T hv hgood
    exact MaxContactCoverGeometry.inStrictNormalCrossingPosition_of_isMaxContactCover T hv hgood
      (MaxContactCoverData.isSmoothDivisor_coverMaxContactIdeal hpb T hv hgood)

end OrderReduction

end FunctorialResolution.EmbeddedResolution

end
