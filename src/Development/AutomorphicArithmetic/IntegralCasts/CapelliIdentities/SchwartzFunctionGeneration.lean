import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

open scoped RestrictedProduct
open Filter Set

private lemma UpperTheory.factorizable_generation {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, T2Space (R i)] {A : ∀ i, Set (R i)} (ho : ∀ i, IsOpen (A i))
    (hc : ∀ i, IsCompact (A i)) {κ : Type*} [Finite κ] (v : ι) (φ : (κ → R v) → ℂ)
    (h1 : IsLocallyConstant φ) (h2 : HasCompactSupport φ) (g : (κ → Πʳ i, [R i, A i]) → ℂ)
    (hg : ∀ x, g x = φ (fun i => x i v) *
      Set.indicator {z : κ → Πʳ i, [R i, A i] | ∀ i u, u ≠ v → z i u ∈ A u} 1 x) :
    IsLocallyConstant g ∧ HasCompactSupport g := by
  classical
  set S : Set (κ → Πʳ i, [R i, A i]) := {z | ∀ i u, u ≠ v → z i u ∈ A u} with hS
  have hSo : IsOpen S := by
    rw [hS, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      (RestrictedProduct.isOpen_forall_imp_mem ho (p := fun u => u ≠ v)).preimage
        (f := fun z : κ → Πʳ i, [R i, A i] => z i) (continuous_apply i)
  have hSc : IsClosed S := by
    simp only [hS, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun u => isClosed_iInter fun _ =>
      (hc u).isClosed.preimage
        ((RestrictedProduct.continuous_eval u).comp (continuous_apply i))
  have hev : Continuous fun (x : κ → Πʳ i, [R i, A i]) (i : κ) => x i v :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  have hK : ∀ K : Set (R v), IsCompact K →
      IsCompact {y : Πʳ i, [R i, A i] | y v ∈ K ∧ ∀ u, u ≠ v → y u ∈ A u} := by
    intro K hK
    have hle : (cofinite : Filter ι) ≤ 𝓟 ({v}ᶜ : Set ι) := by simp
    have hQ : IsCompact (Set.univ.pi (Function.update A v K)) :=
      isCompact_univ_pi fun u => by
        by_cases h : u = v
        · subst h; simpa using hK
        · simpa [h] using hc u
    have hP := (RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
      (S := ({v}ᶜ : Set ι))).isCompact_preimage_iff (K := Set.univ.pi (Function.update A v K))
      (by
        rw [RestrictedProduct.range_coe_principal]
        intro x hx u hu
        have h : u ≠ v := hu
        simpa [h] using hx u trivial) |>.mpr hQ
    convert hP.image (RestrictedProduct.continuous_inclusion hle) using 1
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨⟨y.1, hy2⟩, fun u _ => ?_, rfl⟩
      by_cases h : u = v
      · subst h; rw [Function.update_self]; exact hy1
      · rw [Function.update_of_ne h]; exact hy2 u h
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, fun u hu => z.2 hu⟩
      have := hz v trivial
      rw [Function.update_self] at this
      exact this
  constructor
  · have hI : IsLocallyConstant (S.indicator (1 : (κ → Πʳ i, [R i, A i]) → ℂ)) :=
      (LocallyConstant.indicator (1 : LocallyConstant (κ → Πʳ i, [R i, A i]) ℂ)
        (U := S) ⟨hSc, hSo⟩).isLocallyConstant
    rw [funext hg]
    exact (h1.comp_continuous hev).mul hI
  · refine HasCompactSupport.intro (isCompact_univ_pi fun i : κ =>
      hK _ (h2.isCompact.image (continuous_apply i))) fun x hx => ?_
    rw [hg]
    by_cases hxS : x ∈ S
    · by_contra hne
      refine hx fun i _ => ⟨⟨fun j => x j v, ?_, rfl⟩, hxS i⟩
      exact subset_tsupport _ (left_ne_zero_of_mul hne)
    · rw [Set.indicator_of_notMem hxS, mul_zero]

private lemma UpperTheory.valuation_subring_compact {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] [(Valued.v : Valuation K Γ).RankOne] [LocallyCompactSpace K] :
    IsCompact ((Valued.v : Valuation K Γ).valuationSubring : Set K) := by
  letI := Valued.toNontriviallyNormedField K Γ
  haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact isCompact_iff_compactSpace.mpr
    (Valued.integer.properSpace_iff_compactSpace_integer.mp this)

theorem UpperTheory.schwartz_function_generation :
    ∀ (F : Type) [Field F] [NumberField F],
        (∀ u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), LocallyCompactSpace (u.adicCompletion F)) →
        ∀ (κ : Type) [Fintype κ] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
          (φ : (κ → v.adicCompletion F) → ℂ), IsLocallyConstant φ → HasCompactSupport φ →
          ∀ g : (κ → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) → ℂ,
            (∀ x, g x = φ (fun i => x i v) *
              Set.indicator {z : κ → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F |
                ∀ i u, u ≠ v → z i u ∈ u.adicCompletionIntegers F} 1 x) →
            IsLocallyConstant g ∧ HasCompactSupport g := by
  intro F _ _ hlc κ _ v φ h1 h2 g hg
  exact UpperTheory.factorizable_generation
    (R := fun u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
      u.adicCompletion F)
    (A := fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)
    (fun u => haveI := hlc u; UpperTheory.valuation_subring_compact) v φ h1 h2 g hg
