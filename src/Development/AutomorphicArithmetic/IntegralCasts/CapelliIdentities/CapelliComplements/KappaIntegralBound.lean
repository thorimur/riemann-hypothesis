import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Monotonicity.Lemmas

namespace Bl.KappaIntegralBound

private lemma kappaIntBound {K : Type} [Field K] [NumberField K] (p : Nat.Primes)
    (κ : K →+* PadicComplex p.val) (r : NumberField.RingOfIntegers K) :
    ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := by
  let w : Valuation K NNReal := (NormedField.valuation (K := PadicComplex p.val)).comap κ
  have hi : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K r) :=
    NumberField.RingOfIntegers.isIntegral_coe r
  have hO : IsIntegral w.integer (algebraMap (NumberField.RingOfIntegers K) K r) := hi.tower_top
  have hm : algebraMap (NumberField.RingOfIntegers K) K r ∈ w.integer :=
    (Valuation.integer.integers w).mem_of_integral hO
  rw [Valuation.mem_integer_iff] at hm
  have h2 : ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖₊ ≤ 1 := hm
  exact_mod_cast h2

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [inst_1 : NumberField.{0} K] (p : Nat.Primes)
  (κ : RingHom.{0, 0} K (PadicComplex (Subtype.val.{1} p))),
  Exists.{1} fun (la : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K)) ↦
    ∀ (a : K),
      Iff (LE.le.{0} (DFunLike.coe.{1, 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{0, 0} K la) a) 1)
        (LE.le.{0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} κ a)) 1) := by
  intro K _ _ p κ
  have hle : ∀ r : NumberField.RingOfIntegers K,
      ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := fun r => kappaIntBound p κ r
  let I : Ideal (NumberField.RingOfIntegers K) :=
    { carrier := {r | ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        calc ‖κ (algebraMap _ K c)‖ * ‖κ (algebraMap _ K a)‖
            ≤ 1 * ‖κ (algebraMap _ K a)‖ := mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact ha }
  have hmem : ∀ r, r ∈ I ↔ ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1 :=
    fun r => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]
      simp
    · intro a b hab
      rw [hmem, map_mul, map_mul, norm_mul] at hab
      rw [hmem, hmem]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      have ha := le_antisymm (hle a) h.1
      have hb := le_antisymm (hle b) h.2
      rw [ha, hb, mul_one] at hab
      exact lt_irrefl _ hab
  have hpI : ((p.val : ℕ) : NumberField.RingOfIntegers K) ∈ I := by
    rw [hmem, map_natCast, map_natCast]
    rw [show ((p.val : ℕ) : PadicComplex p.val) = (((p.val : ℕ) : Padic p.val) : PadicComplex p.val)
      from by simp]
    rw [PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  have hne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpI
    have h2 := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hpI
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    exact p.2.ne_zero h2
  let la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) := ⟨I, hIprime, hne⟩
  refine ⟨la, fun a => ?_⟩
  obtain ⟨n, d, h | h⟩ := la.exists_primeCompl_mul_eq_or_mul_eq a
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv : la.valuation K a = la.valuation K (algebraMap _ K n) := by
      rw [← h, map_mul, hvd, mul_one]
    have hN : ‖κ a‖ = ‖κ (algebraMap _ K n)‖ := by
      rw [← h, map_mul, norm_mul, hNd, mul_one]
    rw [hv, hN]
    exact iff_of_true (la.valuation_le_one (K := K) n) (hle n)
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv2 : la.valuation K a * la.valuation K (algebraMap _ K n) = 1 := by
      rw [← map_mul, h, hvd]
    have hN2 : ‖κ a‖ * ‖κ (algebraMap _ K n)‖ = 1 := by
      rw [← norm_mul, ← map_mul, h, hNd]
    have key1 : la.valuation K a ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha
        have h1 : 1 ≤ la.valuation K (algebraMap _ K n) := hv2 ▸ mul_le_of_le_one_left' ha
        exact (la.valuation_eq_one_iff_notMem (K := K)).mp
          (le_antisymm (la.valuation_le_one (K := K) n) h1)
      · intro hn
        have h1 := (la.valuation_eq_one_iff_notMem (K := K)).mpr hn
        rw [h1, mul_one] at hv2
        exact hv2.le
    have key2 : ‖κ a‖ ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha hn
        have h1 : 1 ≤ ‖κ (algebraMap _ K n)‖ := by
          rw [← hN2]; exact mul_le_of_le_one_left (norm_nonneg _) ha
        exact absurd ((hmem n).mp hn) (not_lt.mpr h1)
      · intro hn
        have h1 : ‖κ (algebraMap _ K n)‖ = 1 := le_antisymm (hle n) (not_lt.mp hn)
        rw [h1, mul_one] at hN2
        exact hN2.le
    rw [key1, key2]

end Bl.KappaIntegralBound
