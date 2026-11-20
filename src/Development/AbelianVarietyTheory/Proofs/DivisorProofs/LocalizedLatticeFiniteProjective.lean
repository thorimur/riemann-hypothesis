import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

open TensorProduct GlobalTheory.PerfdLat

namespace GlobalTheory

theorem isLocalizedModule_of_smul_mem {A : Type} [CommRing A] (f : A) {M N : Type}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (L : Submodule A M)
    (hL : ∀ x : M, f • x ∈ L) (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers f) g] :
    IsLocalizedModule (Submonoid.powers f) (g ∘ₗ L.subtype) where
  map_units s := IsLocalizedModule.map_units g s
  surj y := by
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f) g y
    refine ⟨⟨⟨f • x, hL x⟩, ⟨f, Submonoid.mem_powers f⟩ * s⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_smul]
    rw [mul_smul, hx]
    rfl
  exists_of_eq {x y} hxy := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := g) hxy
    exact ⟨c, Subtype.ext hc⟩

theorem localizedModule_finite_projective_of_smul_mem
    (A : Type) [CommRing A] (f : A) (h : ℕ) (L : Submodule A (Fin h → A))
    (hL : ∀ x : Fin h → A, f • x ∈ L) :
    Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) L) ∧
      Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) L) := by
  let g : (Fin h → A) →ₗ[A] (Fin h → Localization.Away f) :=
    LinearMap.pi fun i => Algebra.linearMap A (Localization.Away f) ∘ₗ LinearMap.proj i
  haveI : IsLocalizedModule (Submonoid.powers f) g :=
    IsLocalizedModule.pi (Submonoid.powers f) (fun _ : Fin h => Algebra.linearMap A (Localization.Away f))
  haveI := isLocalizedModule_of_smul_mem f L hL g
  let e := (IsLocalizedModule.iso (Submonoid.powers f) (g ∘ₗ L.subtype)).extendScalarsOfIsLocalization
    (Submonoid.powers f) (Localization.Away f)
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

end GlobalTheory
