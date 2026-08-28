import GppVerify.CelestialHolography.ArithmeticOSGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Arithmetic OS factorization criterion

The decisive AFT step can be isolated abstractly.  If a finite reflected arithmetic
kernel is represented as a Gram kernel

  K(i,j) = <A_i, A_j>

in a genuine Hilbert space, then reflection positivity is automatic.  This file
formalizes only that implication.  It does not construct the arithmetic factor map
`A`, identify the completed prime--Archimedean kernel with such a Gram matrix, or
prove RH.
-/

namespace GppArithmeticOSFactorization

open scoped InnerProductSpace ComplexConjugate

/-- Any finite Hilbert-space Gram kernel is positive semidefinite. -/
theorem gramKernel_posSemidef
    {ι E : Type*} [Finite ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : ι → E) :
    (Matrix.gram ℂ A).PosSemidef := by
  exact Matrix.posSemidef_gram ℂ A

/-- Abstract AFT/OS factorization criterion: once a reflected kernel is identified
with a Hilbert-space Gram matrix, OS positivity follows with no further arithmetic
input.  Thus the hard theorem is the construction/identification of `A`, not the
positivity of a Gram matrix after the factorization is known. -/
theorem kernel_posSemidef_of_gram_factorization
    {ι E : Type*} [Finite ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : Matrix ι ι ℂ) (A : ι → E)
    (hK : K = Matrix.gram ℂ A) :
    K.PosSemidef := by
  rw [hK]
  exact gramKernel_posSemidef A

end GppArithmeticOSFactorization

#print axioms GppArithmeticOSFactorization.gramKernel_posSemidef
#print axioms GppArithmeticOSFactorization.kernel_posSemidef_of_gram_factorization
