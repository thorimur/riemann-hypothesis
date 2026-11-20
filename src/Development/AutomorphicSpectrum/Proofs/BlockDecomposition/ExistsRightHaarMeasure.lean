import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicHaar

theorem exists_haar_rightInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ μ : Measure (GA E a), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  fun E _ _ _ a => ⟨Measure.haar, inferInstance, GlobalTheory.CovolGL.isMulRightInvariant E a _⟩

end GlobalTheory.CompanionTheory.AdelicHaar
