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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem mem_ideal_smul_top_pi_fin_iff {Λ : Type} [CommRing Λ] (J : Ideal Λ) {a : ℕ}
    (y : Fin a → Λ) : y ∈ J • (⊤ : Submodule Λ (Fin a → Λ)) ↔ ∀ i, y i ∈ J := by
  constructor
  · intro h
    refine Submodule.smul_induction_on h ?_ ?_
    · intro r hr m _ i
      exact J.mul_mem_right _ hr
    · intro x z hx hz i
      exact J.add_mem (hx i) (hz i)
  · intro h
    rw [pi_eq_sum_univ y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem chain_le_iInf_sup_pow_smul_top :
    ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ)
      (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
  intro Λ _ I hI a N hanti hpow hstep n x hx
  have hA : Antitone N := antitone_nat_of_succ_le hanti
  have step : ∀ m (y : N m), ∃ z : N (m + 1),
      (y : Fin a → Λ) - z ∈ I ^ (m + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
    intro m y
    obtain ⟨z, hz, w, hw, h⟩ := Submodule.mem_sup.1 (hstep m y.2)
    refine ⟨⟨z, hz⟩, ?_⟩
    have : (y : Fin a → Λ) - z = w := by rw [← h]; abel
    simpa [this] using hw
  choose f hf using step
  let u : ∀ j : ℕ, N (n + j) := fun j =>
    Nat.rec (motive := fun j => N (n + j)) ⟨x, hx⟩ (fun j y => f (n + j) y) j
  have hu0 : (u 0 : Fin a → Λ) = x := rfl
  have hus : ∀ j, (u j : Fin a → Λ) - u (j + 1) ∈
      I ^ (n + j + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := fun j => hf (n + j) (u j)
  have htel : ∀ j j', j ≤ j' → ∀ i, (u j : Fin a → Λ) i - (u j' : Fin a → Λ) i ∈
      I ^ (n + j + 1) := by
    intro j j' hjj i
    induction j', hjj using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have h1 := (mem_ideal_smul_top_pi_fin_iff _ _).1 (hus k) i
      have h2 : I ^ (n + k + 1) ≤ I ^ (n + j + 1) := Ideal.pow_le_pow_right (by omega)
      have h3 := Ideal.add_mem _ ih (h2 h1)
      simpa using h3
  have hlim : ∀ i, ∃ L : Λ, ∀ j, (u j : Fin a → Λ) i - L ∈ I ^ j := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun j => (u j : Fin a → Λ) i) (by
      intro m k hmk
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (by omega) (htel m k hmk i))
    refine ⟨L, fun j => ?_⟩
    have := hL j
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using hlim
  have hdiff : ∀ j, (u j : Fin a → Λ) - L ∈
      I ^ (n + j + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
    intro j
    rw [mem_ideal_smul_top_pi_fin_iff]
    intro i
    have h3 := Ideal.add_mem _ (htel j (n + j + 1) (by omega) i) (hL i (n + j + 1))
    simpa using h3
  have hLmem : L ∈ ⨅ k, N k := by
    rw [Submodule.mem_iInf]
    intro k
    have h1 : (u k : Fin a → Λ) - (u k - L) ∈ N (n + k) :=
      Submodule.sub_mem _ (u k).2 (hpow _ (hdiff k))
    rw [sub_sub_cancel] at h1
    exact hA (by omega) h1
  refine Submodule.mem_sup.2 ⟨L, hLmem, x - L, hdiff 0, by abel⟩

end GlobalTheory
