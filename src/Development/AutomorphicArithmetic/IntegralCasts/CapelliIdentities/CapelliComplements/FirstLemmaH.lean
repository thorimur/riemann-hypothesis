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

namespace Bl.FirstLemmaH

theorem goal1 :
  ∀ {A : Type} (W : Submodule.{0, 0} Complex (A → Complex)),
  FiniteDimensional.{0, 0} Complex (Subtype.{1} fun (x : A → Complex) ↦ Membership.mem.{0, 0} W x) →
    Exists.{1} fun (S : Finset.{0} A) ↦
      ∀ (w : A → Complex),
        Membership.mem.{0, 0} W w → (∀ (a : A), Membership.mem.{0, 0} S a → Eq.{1} (w a) 0) → Eq.{1} w 0 := by
  intro A W hW
  classical
  let f : A → Module.Dual Complex W := fun a =>
    (LinearMap.proj (R := Complex) (φ := fun _ : A => Complex) a).comp W.subtype
  have hfg : (Submodule.span Complex (Set.range f)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hsub, heq⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hmem : ∀ φ ∈ s', ∃ a, f a = φ := fun φ h => hsub h
  choose g hg using hmem
  refine ⟨s'.attach.image (fun φ => g φ.1 φ.2), ?_⟩
  intro w hw h0
  have hker : Submodule.span Complex (s' : Set (Module.Dual Complex W)) ≤
      LinearMap.ker (Module.Dual.eval Complex W ⟨w, hw⟩) := by
    rw [Submodule.span_le]
    intro φ hφ
    have e := hg φ hφ
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
    rw [← e]
    exact h0 _ (Finset.mem_image.2 ⟨⟨φ, hφ⟩, Finset.mem_attach _ _, rfl⟩)
  funext a
  have ha : f a ∈ Submodule.span Complex (s' : Set (Module.Dual Complex W)) :=
    heq ▸ Submodule.subset_span ⟨a, rfl⟩
  have h1 := hker ha
  rw [LinearMap.mem_ker, Module.Dual.eval_apply] at h1
  exact h1

end Bl.FirstLemmaH
