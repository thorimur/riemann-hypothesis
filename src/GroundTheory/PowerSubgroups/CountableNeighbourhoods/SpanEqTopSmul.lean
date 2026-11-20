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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_smul_mem_of_span_eq_top_alt {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → K))
    (hΛ : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (v : Fin n → K) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set (Fin n → K)) := hΛ ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem b hax
    · rw [mul_smul]; exact Λ.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) c
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hsK : algebraMap (𝓞 K) K s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs0
    refine ⟨s * a, mul_ne_zero hs0 ha, ?_⟩
    have e : (s * a) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • x) = r • (a • x) := by
      rw [← algebraMap_smul K (s * a), ← algebraMap_smul K r, ← algebraMap_smul K a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]; exact Λ.smul_mem r hax

end GroundTheory.Variant₂.N1
