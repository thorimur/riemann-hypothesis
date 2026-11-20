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
import Mathlib.NumberTheory.Padics.RingHoms
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

namespace GlobalTheory

theorem exists_padicInt_of_compatible_zmod_pow :
    ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)),
      (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) →
      ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  intro p _ c hc
  let f : ∀ n : ℕ, Polynomial ℤ →+* ZMod (p ^ n) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) (c n)
  have hf : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply Polynomial.ringHom_ext
    · intro a
      simp [f]
    · simpa [f] using hc k₁ k₂ hk
  refine ⟨PadicInt.lift hf Polynomial.X, fun n => ?_⟩
  have h := congrArg (fun g : Polynomial ℤ →+* ZMod (p ^ n) => g Polynomial.X)
    (PadicInt.lift_spec hf n)
  simpa [f] using h

end GlobalTheory
