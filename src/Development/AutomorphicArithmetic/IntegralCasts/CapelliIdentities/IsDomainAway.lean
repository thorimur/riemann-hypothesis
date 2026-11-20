import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop

open AlgebraicGeometry

private lemma exists_kill {A : Type*} [CommRing A] [IsNoetherianRing A] (M : Submonoid A)
    (I : Ideal A) (h : ∀ a ∈ I, ∃ m ∈ M, m * a = 0) :
    ∃ s ∈ M, ∀ a ∈ I, s * a = 0 := by
  classical
  obtain ⟨t, rfl⟩ := (IsNoetherian.noetherian I : I.FG)
  induction t using Finset.induction_on with
  | empty => exact ⟨1, M.one_mem, by simp⟩
  | insert x t _ ih =>
    obtain ⟨s, hs, hs'⟩ := ih fun a ha => h a (Ideal.span_mono (by simp) ha)
    obtain ⟨m, hm, hm'⟩ := h x (Ideal.subset_span (by simp))
    refine ⟨m * s, M.mul_mem hm hs, fun a ha => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at ha
    obtain ⟨c, z, hz, rfl⟩ := ha
    have h2 := hs' z hz
    rw [smul_eq_mul]
    linear_combination (s * c) * hm' + m * h2

private lemma isDomain_away {A L B : Type*} [CommRing A] [CommRing L] [IsDomain L]
    [CommRing B] [Algebra A L] [Algebra A B] (M : Submonoid A) [IsLocalization M L]
    (s : A) (hs : s ∈ M) (hk : ∀ a, algebraMap A L a = 0 → s * a = 0)
    [IsLocalization.Away s B] : IsDomain B := by
  have hu : IsUnit (algebraMap A L s) := IsLocalization.map_units L (⟨s, hs⟩ : M)
  let φ : B →+* L := IsLocalization.Away.lift s hu
  have hφ : ∀ a, φ (algebraMap A B a) = algebraMap A L a := fun a =>
    IsLocalization.Away.lift_eq s hu a
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) b
    have h0 : algebraMap A L a = 0 := by
      rw [← hφ, ← hm, map_mul, hb, zero_mul]
    have h1 : algebraMap A B s * algebraMap A B a = 0 := by
      rw [← map_mul, hk a h0, map_zero]
    have hsu : IsUnit (algebraMap A B s) := IsLocalization.Away.algebraMap_isUnit s
    have h2 : algebraMap A B a = 0 := (hsu.mul_right_eq_zero).mp h1
    have hmu : IsUnit (algebraMap A B (m : A)) :=
      IsLocalization.map_units B m
    simp only at hm
    rw [h2] at hm
    exact (hmu.mul_left_eq_zero).mp hm
  exact hinj.isDomain φ

theorem UpperTheory.Reformulated.B.DYde8.main :
    ∀ {X : AlgebraicGeometry.Scheme} {V : X.Opens},
      AlgebraicGeometry.IsAffineOpen V →
        ∀ [IsNoetherianRing (↑(X.presheaf.obj (Opposite.op V)) : Type)],
          ∀ ξ ∈ V,
            ∀ [IsDomain (↑(X.presheaf.stalk ξ) : Type)],
              ∃ (f : (↑(X.presheaf.obj (Opposite.op V)) : Type)),
                ξ ∈ X.basicOpen f ∧ IsDomain (↑(X.presheaf.obj (Opposite.op (X.basicOpen f))) : Type) := by
  intro X V hV _ ξ hξ _
  letI alg : Algebra Γ(X, V) (X.presheaf.stalk ξ) :=
    X.presheaf.algebra_section_stalk (⟨ξ, hξ⟩ : V)
  let P := (hV.primeIdealOf ⟨ξ, hξ⟩).asIdeal
  have hloc : IsLocalization P.primeCompl (X.presheaf.stalk ξ) :=
    hV.isLocalization_stalk ⟨ξ, hξ⟩
  obtain ⟨s, hs, hk⟩ := exists_kill P.primeCompl
    (RingHom.ker (algebraMap Γ(X, V) (X.presheaf.stalk ξ)))
    (fun a ha => by
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl (X.presheaf.stalk ξ) a).mp ha
      exact ⟨m, m.2, hm⟩)
  refine ⟨s, ?_, ?_⟩
  · have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk ξ) s) :=
      IsLocalization.map_units (X.presheaf.stalk ξ) (⟨s, hs⟩ : P.primeCompl)
    exact (X.mem_basicOpen s ξ hξ).mpr hu
  · have := hV.isLocalization_basicOpen s
    exact isDomain_away (L := X.presheaf.stalk ξ) P.primeCompl s hs (fun a ha => hk a ha)
