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
import Mathlib.RingTheory.Radical.NatInt
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

theorem UpperTheory.semilinear_lattice_mem :
    ∀ (R K C V W : Type) [CommRing R] [Field K] [Field C] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup W] [Module C W] (e : K →+* C) (U : Submodule K V) (Φ : U →ₛₗ[e] W) (A : Set C) (L : AddSubgroup W) (G : Set V), (∀ a ∈ A, ∀ y ∈ L, a • y ∈ L) → (∀ r : R, e (algebraMap R K r) ∈ A) → (∀ g ∈ G, ∃ h : g ∈ U, Φ ⟨g, h⟩ ∈ L) → ∀ (s : R), algebraMap R K s ≠ 0 → e (algebraMap R K s)⁻¹ ∈ A → ∀ v : U, s • (v : V) ∈ Submodule.span R G → Φ v ∈ L := by
  intro R K C V W _ _ _ _ _ _ _ _ _ _ e U Φ A L G hA hR hG s hs hsA v hv
  have key : ∀ x ∈ Submodule.span R G, ∃ h : x ∈ U, Φ ⟨x, h⟩ ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hG x hx
    | zero =>
      refine ⟨U.zero_mem, ?_⟩
      have h0 : (⟨0, U.zero_mem⟩ : U) = 0 := rfl
      rw [h0, map_zero]
      exact L.zero_mem
    | add x y _ _ hx hy =>
      obtain ⟨hxU, hx⟩ := hx
      obtain ⟨hyU, hy⟩ := hy
      refine ⟨U.add_mem hxU hyU, ?_⟩
      have h0 : (⟨x + y, U.add_mem hxU hyU⟩ : U) = ⟨x, hxU⟩ + ⟨y, hyU⟩ := rfl
      rw [h0, map_add]
      exact L.add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨hxU, hx⟩ := hx
      have hm : r • x ∈ U := by
        rw [← algebraMap_smul K r x]
        exact U.smul_mem _ hxU
      refine ⟨hm, ?_⟩
      have h0 : (⟨r • x, hm⟩ : U) = algebraMap R K r • (⟨x, hxU⟩ : U) :=
        Subtype.ext (algebraMap_smul K r x).symm
      rw [h0, LinearMap.map_smulₛₗ]
      exact hA _ (hR r) _ hx
  obtain ⟨hU, hL⟩ := key _ hv
  have h1 : v = (algebraMap R K s)⁻¹ • (⟨s • (v : V), hU⟩ : U) := by
    apply Subtype.ext
    change (v : V) = (algebraMap R K s)⁻¹ • (s • (v : V))
    rw [← algebraMap_smul K s (v : V), inv_smul_smul₀ hs]
  rw [h1, LinearMap.map_smulₛₗ]
  exact hA _ hsA _ hL
