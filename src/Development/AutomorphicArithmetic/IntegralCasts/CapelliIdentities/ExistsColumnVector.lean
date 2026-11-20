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

theorem UpperTheory.Reformulated.B.ExistsColumnVector.ex_col :
    ∀ {k : Type} [inst : Field k] {n : ℕ} (v : Fin (n + (1 : ℕ)) → k),
    v ≠ (0 : Fin (n + (1 : ℕ)) → k) →
      ∃ (q : GL (Fin (n + (1 : ℕ))) k),
        (↑q : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k).mulVec (Pi.single (0 : Fin (n + (1 : ℕ))) (1 : k)) =
          v := by
  intro k _ n v hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  have h1 : ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol i v).det = v i := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  have h2 : (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol i v).submatrix id
      (Equiv.swap 0 i)).det ≠ 0 := by
    rw [Matrix.det_permute', h1]
    refine mul_ne_zero ?_ hi'
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 i)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ h2, ?_⟩
  ext j
  simp [Matrix.mulVec_single_one, Matrix.GeneralLinearGroup.mkOfDetNeZero]
