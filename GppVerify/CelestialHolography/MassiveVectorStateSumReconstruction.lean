import Mathlib.Tactic

/-!
# Massive-vector / scalar state-count reconstruction

This file isolates only the exact state-count algebra justified by the symbolic
adjacent-MHV audit.  It does not identify couplings, color factors, cut orientation,
or loop-measure normalizations with any particular amplitude convention.
-/

namespace GppMassiveVectorStateSumReconstruction

/-- Three equal massive-vector polarization contributions sum to three times the
corresponding scalar contribution. -/
theorem three_equal_vector_states
    (C : ℝ) : C + C + C = 3 * C := by
  ring

/-- In the dimensional-reconstruction convention where the four-dimensional cut is
obtained by subtracting one scalar state from the three-state massive-vector sum,
the resulting state factor is exactly two scalar cuts. -/
theorem four_dimensional_reconstruction
    (Cscalar Cvector C4 : ℝ)
    (hvector : Cvector = 3 * Cscalar)
    (hsub : C4 = Cvector - Cscalar) :
    C4 = 2 * Cscalar := by
  rw [hsub, hvector]
  ring

/-- Equivalent abstract formulation directly from three identical vector states. -/
theorem four_dimensional_reconstruction_from_equal_states
    (Cscalar C4 : ℝ)
    (hsub : C4 = (Cscalar + Cscalar + Cscalar) - Cscalar) :
    C4 = 2 * Cscalar := by
  rw [hsub]
  ring

/-- The same algebra with an arbitrary state multiplicity `D-2`: subtracting one
scalar state leaves the factor `D-3`.  This is an algebraic bookkeeping identity,
not a claim that an arbitrary-dimensional amplitude has already been normalized. -/
theorem dimensional_state_subtraction
    (D Cscalar Cdim Csub : ℝ)
    (hdim : Cdim = (D - 2) * Cscalar)
    (hsub : Csub = Cdim - Cscalar) :
    Csub = (D - 3) * Cscalar := by
  rw [hsub, hdim]
  ring

end GppMassiveVectorStateSumReconstruction

#print axioms GppMassiveVectorStateSumReconstruction.three_equal_vector_states
#print axioms GppMassiveVectorStateSumReconstruction.four_dimensional_reconstruction
#print axioms GppMassiveVectorStateSumReconstruction.four_dimensional_reconstruction_from_equal_states
#print axioms GppMassiveVectorStateSumReconstruction.dimensional_state_subtraction
