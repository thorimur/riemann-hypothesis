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
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatDescent

theorem mem_of_mem_span_of_isBaseChange {A B M M' : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [Module B M'] [IsScalarTower A B M'] {f : M →ₗ[A] M'} (hf : IsBaseChange B f)
    (N : Submodule A M) (w : M) (hw : f w ∈ Submodule.span B (f '' (N : Set M))) : w ∈ N := by
  let g : B ⊗[A] N →ₗ[B] M' := hf.equiv.toLinearMap ∘ₗ N.subtype.baseChange B
  have hspan : Submodule.span B (f '' (N : Set M)) ≤ LinearMap.range g := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨(1 : B) ⊗ₜ[A] (⟨c, hc⟩ : N), by simp [g, IsBaseChange.equiv_tmul]⟩
  obtain ⟨x, hx⟩ := hspan hw
  have h1 : (1 : B) ⊗ₜ[A] w = N.subtype.baseChange B x := by
    apply hf.equiv.injective
    have : hf.equiv (N.subtype.baseChange B x) = f w := hx
    rw [this, IsBaseChange.equiv_tmul, one_smul]
  have hq : N.mkQ ∘ₗ N.subtype = 0 := by
    ext c
    simp
  have h2 : (1 : B) ⊗ₜ[A] (N.mkQ w) = 0 := by
    have := congrArg (N.mkQ.baseChange B) h1
    rw [LinearMap.baseChange_tmul] at this
    rw [this, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hq, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  have h3 : N.mkQ w = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) (M ⧸ N)
    simpa using h2
  simpa using h3

theorem mem_of_mem_span_map :
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  intro K K' _ _ _ _ j n N w hw
  letI := j.toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' :=
    IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')
  have hP : Algebra.IsPushout (𝓞 K) (𝓞 K') K K' :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 K') K'
  have hb : IsBaseChange (𝓞 K')
      ((IsScalarTower.toAlgHom (𝓞 K) K K').toLinearMap.compLeft (Fin n)) :=
    hP.out.finitePow (Fin n)
  exact mem_of_mem_span_of_isBaseChange hb N w hw

end GlobalTheory.FlatDescent
