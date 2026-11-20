import Formalism.GradedWeylDivisibility.FinalD
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

namespace Bl.DualWeylPullback

private lemma map_aeval_nat {O K σ τ : Type} [CommRing O] [CommRing K] (φ : O →+* K)
    (h : σ → MvPolynomial τ O) (f : MvPolynomial σ O) :
    MvPolynomial.map φ (MvPolynomial.aeval h f) =
      MvPolynomial.aeval (fun v => MvPolynomial.map φ (h v)) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hp]

private lemma rowAct_map {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {k n : ℕ}
    (A : Matrix (Fin k) (Fin k) O) (f : MvPolynomial (Fin k × Fin n) O) :
    MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowAct O A f) = Formalism.GradedWeylDivisibility.rowAct K (A.map φ) (MvPolynomial.map φ f) := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  rw [map_aeval_nat]
  congr 1
  congr 1
  funext v
  simp [map_sum]

private lemma colAddGen_map {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {k n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin k × Fin n) O) :
    MvPolynomial.map φ (Formalism.GradedWeylDivisibility.colAddGen O l j f) = Formalism.GradedWeylDivisibility.colAddGen K l j (MvPolynomial.map φ f) := by
  unfold Formalism.GradedWeylDivisibility.colAddGen
  rw [map_aeval_nat]
  congr 1
  congr 1
  funext v
  split_ifs <;> simp

private lemma dualWeyl_pull {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K)
    (hφ : Function.Injective φ) {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) O)
    (hf : MvPolynomial.map φ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢
  refine ⟨?_, ?_⟩
  · intro d hd
    exact hf.1 (by
      rw [MvPolynomial.coeff_map]
      intro h0
      exact hd (hφ (by rw [h0, map_zero])))
  · intro l j hlj
    apply MvPolynomial.map_injective φ hφ
    rw [colAddGen_map, MvPolynomial.map_rename]
    exact hf.2 l j hlj

private lemma span_mat {O K : Type} [CommRing O] [Field K] [Algebra O K] {k : ℕ}
    (g g' : Matrix (Fin k) (Fin k) K) (h : Formalism.MainNotions.G.colSpan O g' ≤ Formalism.MainNotions.G.colSpan O g) :
    ∃ A : Matrix (Fin k) (Fin k) O, g' = g * A.map (algebraMap O K) := by
  have hc : ∀ c : Fin k, ∃ a : Fin k → O, ∑ i, a i • (fun r => g r i) = fun r => g' r c := by
    intro c
    have h1 : (fun r => g' r c) ∈ Formalism.MainNotions.G.colSpan O g' := Submodule.subset_span ⟨c, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun O).1 (h h1)
  choose a ha using hc
  refine ⟨Matrix.of fun i c => a c i, ?_⟩
  ext r c
  have h2 := congrFun (ha c) r
  simp only [Finset.sum_apply, Pi.smul_apply] at h2
  rw [← h2, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [Algebra.smul_def, mul_comm]

private lemma span_unit {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hφ : Function.Injective (algebraMap O K)) {k : ℕ} (g g' : Matrix (Fin k) (Fin k) K)
    (hg : IsUnit g.det) (h : Formalism.MainNotions.G.colSpan O g = Formalism.MainNotions.G.colSpan O g') :
    ∃ A : Matrix (Fin k) (Fin k) O, IsUnit A.det ∧ g' = g * A.map (algebraMap O K) := by
  obtain ⟨A, hA⟩ := span_mat g g' h.ge
  obtain ⟨B, hB⟩ := span_mat g' g h.le
  refine ⟨A, ?_, hA⟩
  have h1 : g * (A * B).map (algebraMap O K) = g * 1 := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc, ← hA, ← hB, Matrix.mul_one]
  have h2 : (A * B).map (algebraMap O K) = 1 := by
    have h3 := congrArg (fun M => g⁻¹ * M) h1
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg] using h3
  have h3 : A * B = 1 := by
    apply Matrix.map_injective hφ
    simpa using h2
  have h4 : A.det * B.det = 1 := by rw [← Matrix.det_mul, h3, Matrix.det_one]
  exact ⟨⟨A.det, B.det, h4, by rw [mul_comm]; exact h4⟩, rfl⟩

private lemma clear_den {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (w : O) (hw : Irreducible w) {σ : Type} (G : MvPolynomial σ K) :
    ∃ n : ℕ, ∃ G0 : MvPolynomial σ O,
      MvPolynomial.map (algebraMap O K) G0 = algebraMap O K (w ^ n) • G := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) G.coeffs
  have hb0 : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hw
  refine ⟨n, ?_⟩
  have hr : algebraMap O K (w ^ n) • G ∈ Set.range (MvPolynomial.map (algebraMap O K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    have hd' : G.coeff d ≠ 0 := by
      intro h0
      apply MvPolynomial.mem_support_iff.1 hd
      rw [MvPolynomial.coeff_smul, h0, smul_zero]
    obtain ⟨y, hy⟩ := hb _ (MvPolynomial.coeff_mem_coeffs _ hd')
    have hu1 : algebraMap O K (↑u⁻¹ : O) * algebraMap O K (↑u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    refine ⟨(↑u⁻¹ : O) * y, ?_⟩
    rw [map_mul, hy, Algebra.smul_def, hu, map_mul]
    linear_combination (algebraMap O K (w ^ n) * G.coeff d) * hu1
  obtain ⟨G0, h0⟩ := hr
  exact ⟨G0, h0⟩

theorem goal1 :
  ∀ {O K : Type} [inst : CommRing.{0} O] [inst_1 : IsDomain.{0} O] [IsDiscreteValuationRing.{0} O] [inst_3 : Field.{0} K]
  [inst_4 : Algebra.{0, 0} O K] [IsFractionRing.{0, 0} O K] (w : O),
  Irreducible.{0} w →
    ∀ (m : Nat) (mu : Fin (HAdd.hAdd.{0, 0, 0} m 1) → Int),
      Antitone.{0, 0} mu →
        ∀ (g : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K),
          IsUnit.{0} (Matrix.det.{0, 0} g) →
            ∀ (F : MvPolynomial.{0, 0} (Prod.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1))) K),
              Membership.mem.{0, 0}
                  (Formalism.GradedWeylDivisibility.dualWeyl.{0} K (HAdd.hAdd.{0, 0, 0} m 1) (HAdd.hAdd.{0, 0, 0} m 1) (Formalism.MainNotions.G.nuOf mu)) F →
                Exists.{1} fun (n : Nat) ↦
                  Membership.mem.{0, 0} (Formalism.MainNotions.G.H0.{0, 0} O m mu (Formalism.MainNotions.G.colSpan.{0, 0} O g))
                    (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} w n) F) := by
  intro O K _ _ _ _ _ _ w hw m mu hmu g hg F hF
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hG : g.det ^ mu (Fin.last m) • Formalism.GradedWeylDivisibility.rowAct K g F ∈
      Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (Formalism.MainNotions.G.nuOf mu) :=
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K _ _ _ g F hF)
  obtain ⟨n, G0, hG0⟩ := clear_den w hw (g.det ^ mu (Fin.last m) • Formalism.GradedWeylDivisibility.rowAct K g F)
  have hG0m : G0 ∈ Formalism.GradedWeylDivisibility.dualWeyl O (m + 1) (m + 1) (Formalism.MainNotions.G.nuOf mu) :=
    dualWeyl_pull _ hinj _ G0 (by rw [hG0]; exact Submodule.smul_mem _ _ hG)
  refine ⟨n, ?_⟩
  unfold Formalism.MainNotions.G.H0
  rw [if_pos hmu]
  simp only [Submodule.mem_iInf]
  rintro g' ⟨hg', hspan⟩
  obtain ⟨A, hA, rfl⟩ := span_unit hinj g g' hg hspan
  rw [Formalism.GradedWeylDivisibility.nablaLTwMem O K m mu _ hg']
  obtain ⟨U, hU⟩ := hA
  refine ⟨(↑(U ^ mu (Fin.last m)) : O) • Formalism.GradedWeylDivisibility.rowAct O A G0,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable O _ _ _ A G0 hG0m), ?_⟩
  change MvPolynomial.map (algebraMap O K) ((↑(U ^ mu (Fin.last m)) : O) • Formalism.GradedWeylDivisibility.rowAct O A G0) = _
  have hz : algebraMap O K ↑(U ^ mu (Fin.last m)) = (algebraMap O K ↑U) ^ mu (Fin.last m) := by
    have h5 : ((Units.map (algebraMap O K).toMonoidHom (U ^ mu (Fin.last m)) : Kˣ) : K) =
        algebraMap O K ↑(U ^ mu (Fin.last m)) := rfl
    rw [← h5, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hdet : (A.map (algebraMap O K)).det = algebraMap O K A.det := by
    rw [RingHom.map_det]
    rfl
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
    rowAct_map, hG0, Matrix.det_mul, hdet, ← hU, hz,
    ← Formalism.GradedWeylDivisibility.rowActMul K (m + 1) (m + 1) (A.map (algebraMap O K)) g, AlgHom.comp_apply,
    ← algebraMap_smul K (w ^ n) F]
  simp only [map_smul, smul_smul]
  congr 1
  rw [mul_zpow]
  ring

end Bl.DualWeylPullback
