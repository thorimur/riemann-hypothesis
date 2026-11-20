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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open MeasureTheory

namespace GlobalTheory

theorem exists_measurableSet_slice_of_transversal
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G)
    (hN : MeasurableSet (N : Set G)) (hM : MeasurableSet (M : Set G))
    (hK : MeasurableSet (K : Set G)) (hσ : Measurable σ)
    (h1 : ∀ x, σ x * x⁻¹ ∈ K ⊓ M) (h2 : ∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x)
    (h3 : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (h4 : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1)
    (DN DM : Set G) (hDN : MeasurableSet DN) (hDM : MeasurableSet DM) :
    ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K,
      (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  have uniq : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, σ k = k → ∀ u' ∈ N, ∀ m' ∈ M, ∀ k' ∈ K, σ k' = k' →
      u * m * k = u' * m' * k' → u = u' ∧ m = m' ∧ k = k' := by
    intro u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    have e : k = m⁻¹ * u⁻¹ * (u' * m' * k') := by rw [← h]; group
    have e1 : (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * (m⁻¹ * m') = k * k'⁻¹ := by rw [e]; group
    have hkk : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
    have hmm : m⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hm) hm'
    have e2 := h4 _ (h3 _ (M.inv_mem hm) _ (N.mul_mem (N.inv_mem hu) hu')) _ hmm (e1 ▸ hkk)
    have huu : u = u' := by
      have : u' = u * (m * (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * m⁻¹) := by group
      rw [this, e2]; group
    rw [e2, one_mul] at e1
    have e3 := h2 (k * k'⁻¹) ⟨hkk, e1 ▸ hmm⟩ k'
    rw [inv_mul_cancel_right, hs, hs'] at e3
    subst huu e3
    exact ⟨rfl, mul_left_cancel (mul_right_cancel h), rfl⟩
  let X : Set (G × G × G) := (DN ∩ N) ×ˢ ((DM ∩ M) ×ˢ ((K : Set G) ∩ {k | σ k = k}))
  have hX : MeasurableSet X :=
    (hDN.inter hN).prod ((hDM.inter hM).prod
      (hK.inter (measurableSet_eq_fun hσ measurable_id)))
  let f : G × G × G → G := fun p => p.1 * p.2.1 * p.2.2
  have hf : Continuous f := by fun_prop
  have hinj : Set.InjOn f X := by
    rintro ⟨u, m, k⟩ ⟨⟨_, hu⟩, ⟨_, hm⟩, hk, hs⟩ ⟨u', m', k'⟩ ⟨⟨_, hu'⟩, ⟨_, hm'⟩, hk', hs'⟩ h
    obtain ⟨a, b, c⟩ := uniq u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    rw [a, b, c]
  refine ⟨f '' X, hX.image_of_continuousOn_injOn hf.continuousOn hinj, ?_⟩
  intro u hu m hm k hk
  have hl := h1 k
  have hl' : k * (σ k)⁻¹ ∈ K ⊓ M := by
    have := (K ⊓ M).inv_mem hl
    simpa using this
  have hσK : σ k ∈ K := by
    have := K.mul_mem hl.1 hk
    simpa using this
  have hσσ : σ (σ k) = σ k := by
    have := h2 _ hl k
    simpa using this
  have hm2 : m * (k * (σ k)⁻¹) ∈ M := M.mul_mem hm hl'.2
  have e : u * m * k = u * (m * (k * (σ k)⁻¹)) * σ k := by group
  constructor
  · rintro ⟨⟨u', m', k'⟩, ⟨⟨hdu, hu'⟩, ⟨hdm, hm'⟩, hk', hs'⟩, h⟩
    obtain ⟨a, b, _⟩ := uniq u hu _ hm2 _ hσK hσσ u' hu' m' hm' k' hk' hs' (e.symm.trans h.symm)
    rw [b, a]
    exact ⟨hdu, hdm⟩
  · rintro ⟨hdu, hdm⟩
    exact ⟨(u, m * (k * (σ k)⁻¹), σ k), ⟨⟨hdu, hu⟩, ⟨hdm, hm2⟩, hσK, hσσ⟩, e.symm⟩

end GlobalTheory
