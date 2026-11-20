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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_setOf_ringHom_comp_eq_of_finite : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K]
    (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  intro A Ω K _ _ _ φ ρ hφ
  classical
  letI : Algebra A Ω := φ.toAlgebra
  haveI : Module.Finite A Ω := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := Ω)
  haveI : Algebra.IsIntegral A Ω := Algebra.IsIntegral.of_finite A Ω
  have hint : ∀ g : Ω, ∃ p : Polynomial A, p.Monic ∧ p.eval₂ φ g = 0 := fun g => by
    obtain ⟨q, hq, he⟩ := Algebra.IsIntegral.isIntegral (R := A) g
    exact ⟨q, hq, he⟩
  choose p hpm hpe using hint
  let F : (Ω →+* K) → (s → K) := fun τ g => τ g
  apply Set.Finite.of_finite_image (f := F)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun g : s => (((p g).map ρ).roots.toFinset : Set K))
      (fun _ => Finset.finite_toSet _)) ?_
    rintro _ ⟨τ, hτ, rfl⟩ g _
    have hτ' : τ.comp φ = ρ := hτ
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm g).map ρ).ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← hτ', ← Polynomial.hom_eval₂, hpe, map_zero]
  · intro τ₁ h₁ τ₂ h₂ he
    have h₁' : τ₁.comp φ = ρ := h₁
    have h₂' : τ₂.comp φ = ρ := h₂
    ext x
    have hx : x ∈ Submodule.span A (s : Set Ω) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact congrFun he ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul, map_mul, hy]
      congr 1
      exact (RingHom.congr_fun h₁' a).trans (RingHom.congr_fun h₂' a).symm

end GlobalTheory
