import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem pow_kills_on_compact_of_local : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) (W : S.Opens), IsCompact (W : Set S) → ∀ (s c : Γ(S, W)), (∀ y ∈ W, ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0) → ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app W).hom (s ^ n * c) = 0 := by
  intro S Φ W hW s c h
  have h' : ∀ y : W, ∃ (V : S.Opens) (hV : V ≤ W), y.1 ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 :=
    fun y => h y.1 y.2
  choose V hV hyV n hn using h'
  obtain ⟨F, hF⟩ := hW.elim_finite_subcover (fun y : W => (V y : Set S)) (fun y => (V y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩)
  refine ⟨∑ y ∈ F, n y, fun T t hΦ => ?_⟩
  apply TopCat.Presheaf.section_ext T.sheaf (t ⁻¹ᵁ W)
  intro x hx
  have hxW : t.base x ∈ (W : Set S) := hx
  obtain ⟨y, hyF, hxy⟩ := Set.mem_iUnion₂.1 (hF hxW)
  have hle : t ⁻¹ᵁ V y ≤ t ⁻¹ᵁ W := fun z hz => hV y hz
  have hxV : x ∈ t ⁻¹ᵁ V y := hxy
  have hN : n y ≤ ∑ y ∈ F, n y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyF
  have key : (T.presheaf.map (homOfLE hle).op).hom ((t.app W).hom (s ^ (∑ y ∈ F, n y) * c)) = 0 := by
    have e := congrArg (fun φ => φ.hom (s ^ (∑ y ∈ F, n y) * c)) (t.naturality (homOfLE (hV y)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    have e2 : s ^ (∑ y ∈ F, n y) * c = s ^ (∑ y ∈ F, n y - n y) * (s ^ n y * c) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]
    refine Eq.trans ?_ (e.symm.trans ?_)
    · rfl
    · rw [e2, map_mul, map_mul, hn y T t hΦ, mul_zero]
  have := congrArg (T.presheaf.germ (t ⁻¹ᵁ V y) x hxV).hom key
  rw [TopCat.Presheaf.germ_res_apply, map_zero] at this
  exact this.trans (map_zero _).symm

end GlobalTheory
