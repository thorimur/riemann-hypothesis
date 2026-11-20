import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
import Mathlib.Topology.Sheaves.Init

open scoped Topology

namespace GlobalTheory

theorem circle_hom_extend_of_injective {A B : Type} [CommGroup A] [CommGroup B] (i : A →* B)
    (hi : Function.Injective i) (ψ : A →* Circle) : ∃ χ : B →* Circle, ∀ a, χ (i a) = ψ a := by
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective (Additive.toMul u)
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    apply Additive.toMul.injective
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [toMul_nsmul, toMul_ofMul]
    rw [← ht, ← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive i) hi (MonoidHom.toAdditive ψ)
  refine ⟨MonoidHom.toAdditive.symm ρ, fun a => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hρ (Additive.ofMul a))

theorem exists_continuous_circle_char_extension :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (ψ : H →* Circle), IsOpen (H : Set G) → Continuous ψ → (∀ x : H, (x : G) ∈ N → ψ x = 1) → ∃ χ : G →* Circle, Continuous χ ∧ (∀ x ∈ N, χ x = 1) ∧ ∀ x : H, χ x = ψ x := by
  intro G _ _ _ H N ψ hH hψ hN
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hker : f.ker ≤ ψ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hN x ((QuotientGroup.eq_one_iff _).1 hx)
  obtain ⟨χ₀, hχ₀⟩ := circle_hom_extend_of_injective (QuotientGroup.kerLift f)
    (QuotientGroup.kerLift_injective f) (QuotientGroup.lift f.ker ψ hker)
  have hx : ∀ x : H, (χ₀.comp (QuotientGroup.mk' N)) x = ψ x := fun x => hχ₀ (QuotientGroup.mk x)
  refine ⟨χ₀.comp (QuotientGroup.mk' N), ?_, fun x hxN => ?_, hx⟩
  · refine continuous_of_continuousAt_one _ ?_
    have hc : ContinuousOn (χ₀.comp (QuotientGroup.mk' N)) (H : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hψ.congr fun x => (hx x).symm
    exact hc.continuousAt (hH.mem_nhds H.one_mem)
  · have : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff _).2 hxN
    rw [MonoidHom.comp_apply, this, map_one]

end GlobalTheory
