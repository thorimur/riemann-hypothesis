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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

universe u_1 u_2 u_3

namespace GlobalTheory.OrthogonalProjectionOnto

open Module

section

variable {R : Type u_1} [Ring R] {ι : Type u_2} [Fintype ι] [DecidableEq ι]
  (M : ι → Type u_3) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem endo_apply_eq (h : ∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0)
    (g : (Π i, M i) →ₗ[R] (Π i, M i)) (x : Π i, M i) (i : ι) :
    g x i = g (Pi.single i (x i)) i := by
  have hx : x = ∑ j, Pi.single j (x j) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [hx]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    have h0 := h j i hji ((LinearMap.proj i).comp (g.comp (LinearMap.single R M j)))
    exact LinearMap.congr_fun h0 (x j)
  · intro hi
    exact absurd (Finset.mem_univ i) hi

def projOnto (h : ∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0) (i₀ : ι) :
    End (End R (Π i, M i)) (Π i, M i) where
  toFun x := fun i => if i = i₀ then x i else 0
  map_add' x y := by
    funext i
    split_ifs <;> simp_all
  map_smul' g x := by
    funext i
    simp only [RingHom.id_apply, Module.End.smul_def]
    rw [endo_apply_eq M h g x i, endo_apply_eq M h g (fun i => if i = i₀ then x i else 0) i]
    split_ifs with hi
    · rfl
    · simp

end

theorem main : ∀ {R : Type u_1} [inst : Ring R] {ι : Type u_2} [Fintype ι] [inst_2 : DecidableEq ι]
    (M : ι → Type u_3) [inst_3 : (i : ι) → AddCommGroup (M i)] [inst_4 : (i : ι) → Module R (M i)]
    [∀ (i : ι), IsSimpleModule R (M i)],
    (∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = (0 : M i →ₗ[R] M j)) →
    ∀ (i₀ : ι) (s : (i : ι) → Finset (M i)), ∃ (r : R), ∀ (i : ι), ∀ m ∈ s i,
      r • m = if i = i₀ then m else (0 : M i) := by
  intro R _ ι _ _ M _ _ _ h i₀ s
  letI : DecidableEq (Π i, M i) := Classical.decEq _
  obtain ⟨r, hr⟩ := jacobson_density (R := R) (M := Π i, M i) (projOnto M h i₀)
    (Finset.univ.biUnion fun i => (s i).image (Pi.single i))
  refine ⟨r, fun i m hm => ?_⟩
  have hmem : Pi.single i m ∈ Finset.univ.biUnion fun i => (s i).image (Pi.single (M := M) i) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    exact ⟨i, m, hm, rfl⟩
  have := congrFun (hr _ hmem) i
  simp only [projOnto, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, Pi.smul_apply] at this
  exact this.symm

end GlobalTheory.OrthogonalProjectionOnto
