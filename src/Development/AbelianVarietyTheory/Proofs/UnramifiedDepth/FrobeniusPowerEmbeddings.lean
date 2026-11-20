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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem exists_forall_eq_pow_of_finite_field (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F]
    (k : Type) [Field k] [CharP k p] (a b : F →+* k) : ∃ n : ℕ, ∀ x, b x = a x ^ p ^ n := by
  have : CharP F p := RingHom.charP a a.injective p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra F k := a.toAlgebra
  have : IsScalarTower (ZMod p) F k :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let b' : F →ₐ[ZMod p] k :=
    { b with
      commutes' := fun r => RingHom.congr_fun
        (Subsingleton.elim (b.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) k)) r }
  obtain ⟨n, hn⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p F (b'.restrictNormal' F)
  refine ⟨n, fun x => ?_⟩
  have h := AlgHom.restrictNormal_commutes b' F x
  have h2 : b'.restrictNormal F x = x ^ p ^ n := by
    have := hn x
    rw [Nat.card_zmod] at this
    exact this
  rw [h2, map_pow] at h
  exact h.symm

theorem exists_forall_eq_pow_of_ker_le (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (k : Type) [Field k] [CharP k p] (σ₀ σ : OE →+* k)
    (h : ∀ x, σ₀ x = 0 → σ x = 0) : ∃ n : ℕ, ∀ x, σ x = σ₀ x ^ p ^ n := by
  let I : Ideal OE := RingHom.ker σ₀
  have : I.IsPrime := RingHom.ker_isPrime σ₀
  have hp : (p : OE ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    simp [I, RingHom.mem_ker]
  have : Module.Finite ℤ (OE ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mk I).toIntAlgHom.toLinearMap
      Ideal.Quotient.mk_surjective
  have : Finite (OE ⧸ I) := by
    refine Module.finite_of_fg_torsion _ (fun x => ⟨⟨(p : ℤ), ?_⟩, ?_⟩)
    · exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    · change (p : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hp, zero_mul]
  let : Field (OE ⧸ I) := (Finite.isField_of_domain (OE ⧸ I)).toField
  obtain ⟨n, hn⟩ := exists_forall_eq_pow_of_finite_field p (OE ⧸ I) k
    (Ideal.Quotient.lift I σ₀ (fun _ hx => hx)) (Ideal.Quotient.lift I σ (fun x hx => h x hx))
  exact ⟨n, fun x => hn (Ideal.Quotient.mk I x)⟩

end GlobalTheory
