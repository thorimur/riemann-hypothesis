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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ker_map_subset_im_map (R C : Type) [CommRing R] [Field C] (f : R →+* C) (ξ ν : R) (N : ℕ)
    (F G : Matrix (Fin N) (Fin N) R) (hξ : ξ ∈ nonZeroDivisors R) (hν : f ν ≠ 0)
    (hfrac : ∀ c : C, ∃ s t : R, f s ≠ 0 ∧ c * f s = f t)
    (hker : ∃ s : R, f s ≠ 0 ∧ ∀ r : R, f r = 0 → ξ ∣ s * r)
    (hGF : G * F = (ξ * ν) • (1 : Matrix (Fin N) (Fin N) R))
    (x : Fin N → C) (hx : F.map f *ᵥ x = 0) : ∃ y : Fin N → C, x = G.map f *ᵥ y := by
  classical
  obtain ⟨s, hs, hsker⟩ := hker
  choose a b ha hab using fun i => hfrac (x i)

  set s0 : R := ∏ i, a i with hs0
  have hs0ne : f s0 ≠ 0 := by
    rw [hs0, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  let t : Fin N → R := fun i => b i * ∏ j ∈ Finset.univ.erase i, a j
  have ht : ∀ i, f (t i) = x i * f s0 := by
    intro i
    have h1 : s0 = a i * ∏ j ∈ Finset.univ.erase i, a j :=
      (Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)).symm
    simp only [t, map_mul, ← hab i]
    rw [h1, map_mul, mul_assoc]
  have hft : (f ∘ t) = f s0 • x := by
    funext i
    simp [ht i, mul_comm]

  have hFt : ∀ i, f ((F *ᵥ t) i) = 0 := by
    intro i
    rw [RingHom.map_mulVec, hft, Matrix.mulVec_smul, hx]
    simp
  choose w hw using fun i => hsker _ (hFt i)
  have hw' : s • (F *ᵥ t) = ξ • w := by
    funext i
    simpa using hw i

  have hG : ξ • ((s * ν) • t) = ξ • (G *ᵥ w) := by
    have h2 : G *ᵥ (s • (F *ᵥ t)) = G *ᵥ (ξ • w) := by rw [hw']
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGF, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h2
    rw [← h2]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcancel : ∀ i, (s * ν) * t i = (G *ᵥ w) i := by
    intro i
    have h3 := congrFun hG i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    exact (mul_cancel_left_mem_nonZeroDivisors hξ).mp h3

  refine ⟨(f s * f ν * f s0)⁻¹ • (f ∘ w), ?_⟩
  funext i
  have h4 : f s * f ν * f s0 ≠ 0 := mul_ne_zero (mul_ne_zero hs hν) hs0ne
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← RingHom.map_mulVec, ← hcancel i, map_mul,
    map_mul, ht i]
  field_simp

end GlobalTheory.DetInv
