import GppVerify.CelestialHolography.HolographicChain
import Mathlib.Tactic

/-!
# Projective covariance of Plücker coordinates

The existing holographic-chain file proves the Plücker relation for a chosen ordered
pair `(v1,v2)` in `ℂ^4`.  To descend from a frame to the Grassmannian point represented
by that frame, one needs the basis-change law: under a `2 × 2` change of frame, all six
Plücker coordinates acquire the same determinant factor.  Therefore their projective
class is frame-independent whenever the change of frame is invertible.
-/

namespace GppGrassmannianPluckerProjective

open GppHolographicChain

/-- A general linear recombination of a two-vector frame. -/
def frameChange
    (a b c d : ℂ) (v1 v2 : Fin 4 → ℂ) : (Fin 4 → ℂ) × (Fin 4 → ℂ) :=
  (fun i => a * v1 i + b * v2 i,
   fun i => c * v1 i + d * v2 i)

/-- **Plücker determinant covariance.**  Every Plücker coordinate of a changed
2-frame is multiplied by the same determinant `a*d - b*c`. -/
theorem plucker_frameChange
    (a b c d : ℂ) (v1 v2 : Fin 4 → ℂ) (i j : Fin 4) :
    let w := frameChange a b c d v1 v2
    plucker w.1 w.2 i j = (a * d - b * c) * plucker v1 v2 i j := by
  dsimp [frameChange, plucker]
  ring

/-- If the frame change has determinant one, the Plücker coordinates are literally
unchanged. -/
theorem plucker_sl2_invariant
    {a b c d : ℂ} (hdet : a * d - b * c = 1)
    (v1 v2 : Fin 4 → ℂ) (i j : Fin 4) :
    let w := frameChange a b c d v1 v2
    plucker w.1 w.2 i j = plucker v1 v2 i j := by
  rw [plucker_frameChange]
  simp [hdet]

/-- For an invertible frame change, the common Plücker scale is nonzero. -/
theorem plucker_common_scale_ne_zero
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    a * d - b * c ≠ 0 := hdet

/-- The Plücker quadratic relation is preserved under every frame change, because
all six coordinates acquire the same common determinant factor.  Here it is stated
at the level of the transformed frame, so it follows from the unconditional relation
already proved for arbitrary vectors. -/
theorem plucker_relation_frameChange
    (a b c d : ℂ) (v1 v2 : Fin 4 → ℂ) :
    let w := frameChange a b c d v1 v2
    plucker w.1 w.2 0 1 * plucker w.1 w.2 2 3
      - plucker w.1 w.2 0 2 * plucker w.1 w.2 1 3
      + plucker w.1 w.2 0 3 * plucker w.1 w.2 1 2 = 0 := by
  dsimp [frameChange]
  exact plucker_relation _ _

end GppGrassmannianPluckerProjective

#print axioms GppGrassmannianPluckerProjective.plucker_frameChange
#print axioms GppGrassmannianPluckerProjective.plucker_sl2_invariant
#print axioms GppGrassmannianPluckerProjective.plucker_relation_frameChange
