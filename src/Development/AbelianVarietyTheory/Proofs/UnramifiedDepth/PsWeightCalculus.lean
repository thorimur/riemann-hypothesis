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
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

open ReciprocityTheory.PGsh

namespace GlobalTheory

theorem psWeight_mul {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    [DecidableEq σ] (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g * g')) := by
  intro α
  rw [MvPowerSeries.coeff_mul]
  refine AddValuation.map_le_sum v ?_
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [AddValuation.map_mul]
  have hs : α.sum (fun j e => ρ j * (e : ℝ)) =
      p.1.sum (fun j e => ρ j * (e : ℝ)) + p.2.sum (fun j e => ρ j * (e : ℝ)) := by
    rw [← hp]
    exact Finsupp.sum_add_index' (fun j => by simp) (fun j a b => by push_cast; ring)
  calc (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      = (((r - p.1.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
        + ((r' - p.2.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)) := by
        rw [← WithTop.coe_add, hs]
        congr 1
        ring
    _ ≤ v (MvPowerSeries.coeff p.1 g) + v (MvPowerSeries.coeff p.2 g') :=
        add_le_add (h p.1) (h' p.2)

theorem psWeight_add {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g + g')) := by
  intro α
  have hc : MvPowerSeries.coeff α (g + g') =
      MvPowerSeries.coeff α g + MvPowerSeries.coeff α g' := map_add _ _ _
  rw [hc]
  refine AddValuation.map_le_add v ?_ ?_
  · exact le_trans (WithTop.coe_le_coe.mpr (sub_le_sub_right (min_le_left r r') _)) (h α)
  · exact le_trans (WithTop.coe_le_coe.mpr (sub_le_sub_right (min_le_right r r') _)) (h' α)

theorem psWeight_pow {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    [DecidableEq σ] (ρ : σ → ℝ) (g : MvPowerSeries σ C) (r : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g)) (N : ℕ) :
    ∀ α, (((N * r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g ^ N)) := by
  induction N with
  | zero =>
    intro α
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs with hα
    · subst hα
      simp
    · rw [AddValuation.map_zero]
      exact le_top
  | succ n ih =>
    intro α
    rw [pow_succ]
    have e : ((n + 1 : ℕ) : ℝ) * r = n * r + r := by push_cast; ring
    rw [e]
    exact psWeight_mul v ρ (g ^ n) g (n * r) r ih h α

theorem psWeight_calculus :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ),
    (∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g))) → ((∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g'))) → (∀ α, (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g * g'))) ∧ (∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g + g')))) ∧ ∀ N : ℕ, (∀ α, (((N * r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g ^ N)))) := by
  intro C _ v σ _ _ ρ g g' r r' h
  exact ⟨fun h' => ⟨psWeight_mul v ρ g g' r r' h h', psWeight_add v ρ g g' r r' h h'⟩,
    fun N => psWeight_pow v ρ g r h N⟩

end GlobalTheory
