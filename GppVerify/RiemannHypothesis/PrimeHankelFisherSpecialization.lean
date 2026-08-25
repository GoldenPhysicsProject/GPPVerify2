import GppVerify.RiemannHypothesis.PrimeHankelInfiniteLift
import GppVerify.RiemannHypothesis.ZetaFisherStrictMonotonicity

/-!
# Prime-gas Fisher specialization of the infinite polynomial Gram theorem

This file instantiates the abstract infinite weighted-polynomial positivity theorem
with the actual arithmetic Fisher weights

  Λ(n) log(n) exp(-β log n).

The only remaining analytic input for the completely unconditional all-order Hankel
statement is summability of the polynomial-square weighted series itself.
-/

namespace GppPrimeHankelFisherSpecialization

open Polynomial BigOperators
open GppPrimeHankelInfiniteLift
open GppZetaFisherStrictMonotonicity

/-- Strict positivity for the actual prime-gas Fisher weights, once a finite
positive-support witness and summability of the polynomial-square series are given. -/
theorem fisher_polynomial_tsum_pos
    {β : ℝ} (p : ℝ[X]) (S : Finset ℕ) (N : ℕ)
    (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N)
    (hcard : N < (S.image (fun n : ℕ => Real.log n)).card)
    (hwS : ∀ n ∈ S, 0 < fisherSummand β n)
    (hsum : Summable
      (fun n : ℕ => fisherSummand β n * (p.eval (Real.log n)) ^ 2)) :
    0 < ∑' n : ℕ, fisherSummand β n * (p.eval (Real.log n)) ^ 2 := by
  exact weighted_polynomial_tsum_pos
    p (fun n : ℕ => Real.log n) (fisherSummand β) S N
    hp hdeg hcard
    (fisherSummand_nonneg β)
    hwS hsum

end GppPrimeHankelFisherSpecialization

#print axioms GppPrimeHankelFisherSpecialization.fisher_polynomial_tsum_pos
