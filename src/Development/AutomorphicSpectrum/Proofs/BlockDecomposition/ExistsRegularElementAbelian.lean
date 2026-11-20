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
import Mathlib.GroupTheory.CosetCover
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
import Mathlib.Topology.Sheaves.Init
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

theorem exists_regular_point : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j →
      ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  classical
  intro n 𝔞 U
  let L : Fin n × Fin n → (↥𝔞 →ₗ[ℝ] ℂ) := fun p =>
    { toFun := fun A => (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2
      map_add' := by
        intro A B
        simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        ring
      map_smul' := by
        intro c A
        simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          RingHom.id_apply, smul_sub] }
  have hL : ∀ (p : Fin n × Fin n) (A : ↥𝔞), L p A =
      (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2 := fun _ _ => rfl
  let s : Finset (Submodule ℝ ↥𝔞) :=
    (Finset.univ.image fun p => LinearMap.ker (L p)).erase ⊤
  have hs : (⊤ : Submodule ℝ ↥𝔞) ∉ s := Finset.notMem_erase _ _
  obtain ⟨H, hH⟩ := (Set.ne_univ_iff_exists_notMem _).1
    (Subspace.biUnion_ne_univ_of_top_notMem hs)
  refine ⟨H, H.2, fun i j hij A hA => ?_⟩
  have hker : H ∈ LinearMap.ker (L (i, j)) := by
    rw [LinearMap.mem_ker, hL]
    exact sub_eq_zero.2 hij
  have htop : LinearMap.ker (L (i, j)) = ⊤ := by
    by_contra hne
    apply hH
    refine Set.mem_biUnion (x := LinearMap.ker (L (i, j))) ?_ hker
    exact Finset.mem_coe.2 (Finset.mem_erase.2
      ⟨hne, Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩)
  have hA' : (⟨A, hA⟩ : ↥𝔞) ∈ LinearMap.ker (L (i, j)) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hA'
  exact sub_eq_zero.1 hA'

end GlobalTheory.CompanionTheory.IwaGen
