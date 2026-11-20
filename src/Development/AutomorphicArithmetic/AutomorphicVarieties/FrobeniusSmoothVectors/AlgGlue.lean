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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_glue :
    ∀ {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing D] [Algebra O D] (𝔪 : Ideal D), ⨅ N : ℕ, 𝔪 ^ N = ⊥ → ∀ f : ∀ N : ℕ, A →ₐ[O] D ⧸ 𝔪 ^ (N + 1), (∀ a, ∃ d, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N a) → ∃ ξ : A →ₐ[O] D, ∀ a N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ a) = f N a := by
  intro O A D _ _ _ _ _ 𝔪 hm f hf
  choose g hg using hf
  have uniq : ∀ x y : D, (∀ N : ℕ, Ideal.Quotient.mk (𝔪 ^ (N + 1)) x
      = Ideal.Quotient.mk (𝔪 ^ (N + 1)) y) → x = y := by
    intro x y h
    have hxy : x - y ∈ (⨅ N : ℕ, 𝔪 ^ N) := by
      rw [Ideal.mem_iInf]
      intro N
      exact Ideal.pow_le_pow_right (Nat.le_succ N) (Ideal.Quotient.eq.1 (h N))
    rw [hm, Ideal.mem_bot] at hxy
    exact sub_eq_zero.1 hxy
  refine ⟨{ toFun := g
            map_one' := uniq _ _ fun N => by rw [hg, map_one, map_one]
            map_mul' := fun a b => uniq _ _ fun N => by rw [hg, map_mul, map_mul, hg, hg]
            map_zero' := uniq _ _ fun N => by rw [hg, map_zero, map_zero]
            map_add' := fun a b => uniq _ _ fun N => by rw [hg, map_add, map_add, hg, hg]
            commutes' := fun r => uniq _ _ fun N => by
              rw [hg, AlgHom.commutes]; rfl }, fun a N => hg a N⟩
