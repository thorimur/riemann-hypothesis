import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory

theorem exists_perm_of_univ_map_eq {ι β : Type} [Fintype ι] (g g' : ι → β)
    (h : Finset.univ.val.map g = Finset.univ.val.map g') :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = g' i := by
  classical
  have hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this.symm
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

theorem eq_of_perm_inv_invariant_of_multiset_eq :
    ∀ (m : ℕ) (f : (Fin m → ℂ) → ℂ), (∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) → (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧ ∀ i, f (Function.update α i (α i)⁻¹) = f α) → ∀ α α' : Fin m → ℂ, (∀ i, α i ≠ 0) → Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) = Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) → f α = f α' := by
  classical
  intro m f hf α α' hα h
  have hα' : ∀ i, α' i ≠ 0 := by
    intro i hi
    have hmem : (0 : ℂ) ∈ Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, hi⟩))
    rw [← h] at hmem
    rcases Multiset.mem_add.1 hmem with h1 | h1
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j hj
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j (inv_eq_zero.1 hj)
  have h2 := congrArg (Multiset.map (fun x : ℂ => x + x⁻¹)) h
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => (γ i)⁻¹ + γ i) = fun i => γ i + (γ i)⁻¹ :=
    fun γ => funext fun i => add_comm _ _
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => α i + (α i)⁻¹)
      = Finset.univ.val.map (fun i => α' i + (α' i)⁻¹) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    have h4 := hπ i
    have ha := hα (π i)
    have hb := hα' i
    have h5 : (α' i - α (π i)) * (α' i * α (π i) - 1) = 0 := by
      field_simp at h4
      linear_combination -h4
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact Or.inl (sub_eq_zero.1 h6)
    · exact Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h6))
  have hβ : ∀ i, (α ∘ π) i ≠ 0 := fun i => hα _
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      have hne : ∀ i, (fun i => if i ∈ s then α' i else (α ∘ π) i) i ≠ 0 := by
        intro i
        by_cases hi : i ∈ s
        · simpa [hi] using hα' i
        · simpa [hi] using hα (π i)
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf _ hne).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α hα).1 π, ← this]

end GlobalTheory
