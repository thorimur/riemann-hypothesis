import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.Topology.Sheaves.Presheaf

namespace Bl.general_b_fact_left_further

theorem goal1 :
  ∀ {n : Nat} {mu : Fin n → Int},
  Formalism.MainNotions.G.Dominant mu → ∀ (c : Int) (m : Fin n), Iff (LE.le.{0} c (mu m)) (LT.lt.{0} m.val (Formalism.MainNotions.G.colH mu c)) := by
  intro n mu hd c m
  have ha : Antitone mu := hd
  unfold Formalism.MainNotions.G.colH
  constructor
  · intro h
    have hsub : Finset.Iic m ⊆ Finset.univ.filter (fun k => c ≤ mu k) := by
      intro k hk
      rw [Finset.mem_Iic] at hk
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ k, le_trans h (ha hk)⟩
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h1
    omega
  · intro h
    by_contra hc
    have hsub : Finset.univ.filter (fun k => c ≤ mu k) ⊆ Finset.Iio m := by
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_Iio]
      by_contra hkm
      have hmk : m ≤ k := not_lt.mp hkm
      exact hc (le_trans hk.2 (ha hmk))
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h1
    omega

end Bl.general_b_fact_left_further
