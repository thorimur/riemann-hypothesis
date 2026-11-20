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
open NumberField
open scoped TensorProduct NNReal
open Classical

theorem UpperTheory.WildB.embSum :
    ∀ (E : Type) [Field E] [NumberField E] (d : 𝓞 E), d ≠ 0 → ∀ (n : ℕ) (a b : Fin n → 𝓞 E), (∀ x : E, ∑ j, Algebra.trace ℚ E (x * (b j : E) / (d : E)) • (a j : E) = x) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (φ ψ : E →+* C), ∑ j, φ (a j : E) * ψ (b j : E) = if ψ = φ then φ (d : E) else 0 := by
  intro E _ _ d hd0 n a b h C _ _ _ φ ψ
  have hd : (d : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hd0
  have htr : ∀ y : E, ((Algebra.trace ℚ E y : ℚ) : C) = ∑ χ : E →+* C, χ y := by
    intro y
    have h1 := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := C) (x := y)
    rw [eq_ratCast] at h1
    rw [h1]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E C) _ _ (fun χ => rfl)).symm
  have hli : LinearIndependent C (fun χ : E →+* C => (χ : E → C)) :=
    (linearIndependent_monoidHom E C).comp (fun χ : E →+* C => (χ : E →* C))
      (fun χ χ' hh => RingHom.ext fun x => DFunLike.congr_fun hh x)
  have key : ∑ χ : E →+* C, ((∑ j, φ (a j : E) * χ (b j : E)) / χ (d : E) - if χ = φ then 1 else 0) • (χ : E → C) = 0 := by
    funext x
    have h2 := congrArg φ (h x)
    rw [map_sum] at h2
    simp only [Rat.smul_def, map_mul, map_ratCast] at h2
    simp only [htr, map_mul, map_div₀] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply]
    rw [← h2, sub_eq_zero]
    simp only [Finset.sum_mul, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun χ _ => by ring
  have h3 := Fintype.linearIndependent_iff.1 hli _ key ψ
  have hψ : ψ (d : E) ≠ 0 := (map_ne_zero ψ).2 hd
  rw [sub_eq_zero, div_eq_iff hψ] at h3
  rw [h3]
  split_ifs with hh
  · rw [hh, one_mul]
  · rw [zero_mul]
