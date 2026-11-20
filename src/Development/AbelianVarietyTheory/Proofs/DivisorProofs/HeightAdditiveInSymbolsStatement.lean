import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAdditiveInSymbols
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_additive_in_symbols : ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
    ∀ (c : O.s.Comp) (x : (O.var c).X) {ι : Type} (s : Finset ι) (a : ι → Sym D.host.E) (n : ι → ℤ),
    (∀ i ∈ s, (a i).1 = (fun _ => false) ∧ (a i).2.1 = none) →
    (adlOf (O.Φ.C c) (O.met.hm c) (∑ i ∈ s, Finsupp.single (a i) (n i))).ht x =
      ∑ i ∈ s, (n i : ℝ) * (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (a i) 1)).ht x := by
  first | exact @GlobalTheory.HtAdd.ht_adlOf_sum | exact GlobalTheory.HtAdd.ht_adlOf_sum | (intros; apply GlobalTheory.HtAdd.ht_adlOf_sum <;> assumption)
