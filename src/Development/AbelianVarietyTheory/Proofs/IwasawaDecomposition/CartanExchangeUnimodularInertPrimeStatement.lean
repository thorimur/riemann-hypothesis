import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartanExchangeUnimodularInertPrime
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_exchange_unimodular_inert_prime : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ), CartanInert E n := by
  first | exact @GlobalTheory.CartanInertPf.cartanInert | exact GlobalTheory.CartanInertPf.cartanInert | (intros; apply GlobalTheory.CartanInertPf.cartanInert <;> assumption)
