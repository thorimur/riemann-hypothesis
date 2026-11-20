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

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (I J : Ideal R) (n : ℕ), J ^ n ≤ I → I ≤ J → IsAdicComplete I M → IsAdicComplete J M := by
  intro R M _ _ _ I J n hn hIJ hI
  have hle : ∀ k, J ^ ((n + 1) * k) • (⊤ : Submodule R M) ≤ I ^ k • ⊤ := fun k => by
    apply Submodule.smul_mono_left
    calc J ^ ((n + 1) * k) ≤ J ^ (n * k) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right k (Nat.le_succ n))
      _ = (J ^ n) ^ k := pow_mul J n k
      _ ≤ I ^ k := Ideal.pow_right_mono hn k
  have hge : ∀ k, I ^ k • (⊤ : Submodule R M) ≤ J ^ k • ⊤ := fun k =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ k)
  refine
    { haus' := fun x hx => hI.toIsHausdorff.haus' x fun k => (hx ((n + 1) * k)).mono (hle k)
      prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' (fun k => f ((n + 1) * k))
    (fun {a b} hab => (hf (Nat.mul_le_mul_left (n + 1) hab)).mono (hle a))
  refine ⟨L, fun m => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left m (Nat.succ_pos n))).trans ((hL m).mono (hge m))
