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

theorem _root_.UpperTheory.KN.admissible_lattices_commensurable :
    ∀ {O LL V : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (Λ A : Submodule O V), Λ.FG → ∀ c : O, c ≠ 0 →
      ∃ μ : O, μ ≠ 0 ∧ ∀ u ∈ Λ, μ • u ∈ A → ∃ a ∈ A, μ • u = c • a := by
  intro O LL V _ _ _ _ _ _ _ _ _ _ Λ A hΛ c hc
  haveI : IsNoetherian O Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  let f : ℕ →o Submodule O Λ :=
    ⟨fun n => (A.comap ((c ^ n) • LinearMap.id : V →ₗ[O] V)).comap Λ.subtype, by
      intro m n hmn x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hx ⊢
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, mul_comm, mul_smul]
      exact A.smul_mem _ hx⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) f
  refine ⟨c ^ (N + 1), pow_ne_zero _ hc, ?_⟩
  intro u hu hμ
  have h1 : (⟨u, hu⟩ : Λ) ∈ f (N + 1) := hμ
  rw [← hN (N + 1) (Nat.le_succ N)] at h1
  have h2 : c ^ N • u ∈ A := h1
  exact ⟨c ^ N • u, h2, by rw [pow_succ, mul_comm, mul_smul]⟩
