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
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
open scoped TensorProduct

namespace GlobalTheory

theorem weightSpace_tensor_ringHom_pos : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (χ : C →+* k), 0 < Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ χ
  let φ : k ⊗[ℤ] C →ₐ[k] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)
  have hφs : Function.Surjective φ := fun a => ⟨algebraMap k (k ⊗[ℤ] C) a, by rw [φ.commutes]; rfl⟩
  let m : Ideal (k ⊗[ℤ] C) := RingHom.ker φ
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφs
  haveI : IsArtinianRing (k ⊗[ℤ] C) := IsArtinianRing.of_finite k (k ⊗[ℤ] C)
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (m ^ j), fun a b h => Ideal.pow_le_pow_right h⟩ :
      ℕ →o (Ideal (k ⊗[ℤ] C))ᵒᵈ)
  have hst : ∀ j, N ≤ j → m ^ N = m ^ j := fun j hj => hN j hj
  have hJJ : IsIdempotentElem (m ^ (N + 1)) := by
    show m ^ (N + 1) * m ^ (N + 1) = m ^ (N + 1)
    rw [← pow_add, ← hst (N + 1 + (N + 1)) (by omega), hst (N + 1) (by omega)]
  obtain ⟨e, he, hJe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian (m ^ (N + 1)))).mp hJJ
  have hJe' : m ^ (N + 1) = Ideal.span {e} := hJe
  have hv : (1 - e : k ⊗[ℤ] C) ≠ 0 := by
    intro h
    have h1 : e = 1 := (sub_eq_zero.mp h).symm
    have : m ^ (N + 1) = ⊤ := by rw [hJe', h1, Ideal.span_singleton_one]
    exact hm.ne_top (top_le_iff.mp (this ▸ Ideal.pow_le_self (by omega)))
  have key : ∀ x ∈ m, x ^ (N + 1) * (1 - e) = 0 := by
    intro x hx
    have hx' : x ^ (N + 1) ∈ Ideal.span {e} := hJe' ▸ Ideal.pow_mem_pow hx (N + 1)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    rw [← ha, mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]
  refine lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 ?_)
  rw [Submodule.ne_bot_iff]
  refine ⟨1 - e, ?_, hv⟩
  rw [Submodule.mem_iInf]
  intro c
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨N + 1, ?_⟩
  let x : k ⊗[ℤ] C := (1 : k) ⊗ₜ c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hxm : x ∈ m := by
    simp [m, x, φ, RingHom.mem_ker]
  have hf : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c) - χ c • (1 : Module.End k (k ⊗[ℤ] C))
      = Algebra.lmul k (k ⊗[ℤ] C) x := by
    ext y
    simp [x, sub_mul, Algebra.smul_def]
  rw [hf, ← map_pow]
  simpa using key x hxm

end GlobalTheory
