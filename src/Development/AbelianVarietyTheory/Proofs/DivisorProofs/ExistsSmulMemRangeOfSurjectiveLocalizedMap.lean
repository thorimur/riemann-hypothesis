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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_smul_mem_range_of_surjective_localization_map
    (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B)
    (hs : Function.Surjective (Algebra.TensorProduct.map
      (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ)) :
    ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  intro b
  classical
  set L := Localization.AtPrime p
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  let π := N.mkQ
  let g : L ⊗[R] B →ₗ[R] L ⊗[R] (B ⧸ N) := LinearMap.lTensor L π
  obtain ⟨z, hz⟩ := hs ((1 : L) ⊗ₜ[R] b)
  have key : ∀ w : L ⊗[R] A, g (Algebra.TensorProduct.map
      (AlgHom.id L L) ψ w) = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul]
      simp only [g, LinearMap.lTensor_tmul]
      have : π (ψ y) = 0 := by
        simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨y, rfl⟩
      rw [this, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have h0 : (TensorProduct.mk R L (B ⧸ N) 1) (π b) = 0 := by
    have := key z
    rw [hz] at this
    simpa [g] using this
  have hloc : IsLocalizedModule p.primeCompl (TensorProduct.mk R L (B ⧸ N) 1) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl L _).mpr (TensorProduct.isBaseChange R _ L)
  obtain ⟨s, hs'⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl _).mp h0
  refine ⟨s, s.2, ?_⟩
  have : π ((s : R) • b) = 0 := by
    rw [map_smul]; exact hs'
  simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

end GlobalTheory
