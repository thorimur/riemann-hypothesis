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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem mem_adjoin_div_of_fixed : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ (S : Set Ω) (x : Ω), (∀ g : Ω ≃ₐ[R] Ω, (∀ s ∈ S, g s = s) → g x = x) → ∃ b ∈ Algebra.adjoin R S, ∃ c ∈ Algebra.adjoin R S, c ≠ 0 ∧ x = b / c := by
  intro R Ω _ _ _ _ _ _ _ hinj S x hx
  set A := Algebra.adjoin R S with hA
  set F : Subfield Ω := Subfield.closure (A : Set Ω) with hF
  have hAF : ∀ y ∈ A, y ∈ F := fun y hy => Subfield.subset_closure hy
  let φ : R →+* F := (algebraMap R Ω).codRestrict F (fun r => hAF _ (A.algebraMap_mem r))
  have hφ : ∀ r, algebraMap F Ω (φ r) = algebraMap R Ω r := fun r => rfl
  haveI : Algebra.IsAlgebraic F Ω := by
    constructor
    intro y
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) y
    refine ⟨p.map φ, ?_, ?_⟩
    · intro h
      apply hp0
      have hφi : Function.Injective φ := by
        intro a b hab
        apply hinj
        have := congrArg (algebraMap F Ω) hab
        simpa [hφ] using this
      exact (Polynomial.map_eq_zero_iff hφi).mp h
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      rw [Polynomial.aeval_def] at hp
      convert hp using 2
      exact RingHom.ext hφ
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  haveI : CharZero F := RingHom.charZero (algebraMap F Ω)
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfix : ∀ f : Ω ≃ₐ[F] Ω, f x = x := by
    intro f
    have hfF : ∀ y ∈ F, f y = y := fun y hy => f.commutes ⟨y, hy⟩
    let g : Ω ≃ₐ[R] Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => hfF _ (hAF _ (A.algebraMap_mem r)))
    exact hx g (fun s hs => hfF _ (hAF _ (Algebra.subset_adjoin hs)))
  have hxF : x ∈ F := by
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) x).mpr hfix
    rw [← hy]; exact y.2
  obtain ⟨b, hb, c, hc, hbc⟩ := Subfield.mem_closure_iff.mp hxF
  have hcl : ∀ y ∈ Subring.closure (A : Set Ω), y ∈ A := fun y hy =>
    (Subring.closure_le (t := A.toSubring)).mpr (fun z hz => hz) hy
  by_cases hc0 : c = 0
  · refine ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, ?_⟩
    rw [← hbc, hc0]; simp
  · exact ⟨b, hcl _ hb, c, hcl _ hc, hc0, hbc.symm⟩

end GlobalTheory
