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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Matrix

theorem GlobalTheory.isotropic_finrank_le_card (K : Type) [Field K] (κ : Type) [Fintype κ]
    (L : Submodule K ((κ → K) × (κ → K)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) :
    Module.finrank K L ≤ Fintype.card κ := by
  classical
  let ψ : ((κ → K) × (κ → K)) →ₗ[K] Module.Dual K ((κ → K) × (κ → K)) :=
    LinearMap.mk₂ K (fun a b => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (by intro a a' b; simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (by intro c a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (by intro a b b'; simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (by intro c a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    have h1 : ∀ i, a.1 i = 0 := by
      intro i
      have := LinearMap.congr_fun ha ((0 : κ → K), Pi.single i 1)
      simpa [ψ, dotProduct_single] using this
    have h2 : ∀ i, a.2 i = 0 := by
      intro i
      have := LinearMap.congr_fun ha ((Pi.single i 1 : κ → K), 0)
      simpa [ψ, single_dotProduct] using this
    ext i
    · exact h1 i
    · exact h2 i
  let g : L →ₗ[K] L.dualAnnihilator :=
    (ψ.comp L.subtype).codRestrict L.dualAnnihilator (by
      intro x
      rw [Submodule.mem_dualAnnihilator]
      intro b hb
      show (x : (κ → K) × (κ → K)).1 ⬝ᵥ b.2 - b.1 ⬝ᵥ (x : (κ → K) × (κ → K)).2 = 0
      rw [hL _ x.2 b hb, sub_self])
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hψ
    have := congrArg Subtype.val hxy
    simpa [g] using this
  have h3 := LinearMap.finrank_le_finrank_of_injective hg
  have h4 := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  have h5 : Module.finrank K ((κ → K) × (κ → K)) = Fintype.card κ + Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  omega
