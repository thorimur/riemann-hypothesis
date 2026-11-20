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

theorem UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq :
    ∀ {n : ℕ} {z z' : Fin n → ℂˣ},
      Multiset.map (fun (i : Fin n) ↦ (↑(z i) : ℂ)) Finset.univ.val =
          Multiset.map (fun (i : Fin n) ↦ (↑(z' i) : ℂ)) Finset.univ.val →
        ∃ (σ : Equiv.Perm (Fin n)), z' = z ∘ (⇑σ : Fin n → Fin n) := by
  classical
  intro n z z' h
  have key : ∀ (w : Fin n → ℂˣ) (c : ℂ),
      Fintype.card {i : Fin n // (w i : ℂ) = c} =
        Multiset.count c (Multiset.map (fun (i : Fin n) ↦ (↑(w i) : ℂ)) Finset.univ.val) := by
    intro w c
    rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i : Fin n // (z' i : ℂ) = c} =
      Fintype.card {i : Fin n // (z i : ℂ) = c} := by
    intro c
    rw [key, key, h]
  let e : ∀ c : ℂ, {i : Fin n // (z' i : ℂ) = c} ≃ {i : Fin n // (z i : ℂ) = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e, ?_⟩
  funext i
  apply Units.ext
  exact (Equiv.ofFiberEquiv_map (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e i).symm
