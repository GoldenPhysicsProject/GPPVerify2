import Mathlib.Tactic

/-!
# The Spin(10) half-spin occupation basis and Standard Model weights

Let W = C^5 = C^3 ⊕ C^2, with the primitive traceless
SU(5) cocharacter H6 = diag(-2,-2,-2,3,3).
The even-degree exterior Fock basis has 16 states:
  Λ^even W = Λ^0 W ⊕ Λ^2 W ⊕ Λ^4 W.

The weight 6Y of a basis wedge S is the sum of the weights
of its occupied modes: 3|S| - 5|S ∩ {0,1,2}|.
The resulting six sectors are precisely the left-handed Standard
Model generation, including the charge-conjugated right neutrino.

This file formalizes only the finite exterior-basis weights/counts
and their anomaly sums. It does NOT construct the Clifford/Spin(10)
action, derive the C^3⊕C^2 splitting from the holographic boundary,
or promote the stabilizer into a dynamical gauge group.
-/

namespace GppSpinTenExteriorSpectrum

/-- The five internal fermionic modes of the complex polarization. -/
abbrev Mode := Fin 5

/-- Even occupation states (subsets of degrees 0, 2 and 4). -/
def evenBasis : Finset (Finset Mode) :=
  (Finset.univ : Finset Mode).powerset.filter (fun s => s.card % 2 = 0)

/-- Number of occupied colour modes among the first three. -/
def colorCount (s : Finset Mode) : ℕ :=
  (s.filter (fun i : Mode => i.val < 3)).card

/-- Integral primitive hypercharge weight H6 = 6Y. -/
def chargeSix (s : Finset Mode) : ℤ :=
  3 * (s.card : ℤ) - 5 * (colorCount s : ℤ)

/-- A sector is selected by total exterior degree and colour occupancy. -/
def sector (degree color : ℕ) : Finset (Finset Mode) :=
  evenBasis.filter (fun s => s.card = degree ∧ colorCount s = color)

/-- The positive half-spin occupation basis contains exactly 16 states. -/
theorem even_occupation_card : evenBasis.card = 16 := by
  native_decide

/-- Standard Model multiplet counts:
ν^c:1, e^c:1, Q:6, u^c:3, d^c:3, L:2. -/
theorem six_sector_counts :
    (sector 0 0).card = 1 ∧
    (sector 2 0).card = 1 ∧
    (sector 2 1).card = 6 ∧
    (sector 2 2).card = 3 ∧
    (sector 4 2).card = 3 ∧
    (sector 4 3).card = 2 := by
  native_decide

/-- Every even-basis state lies in one of the six physical sectors. -/
theorem sector_exhaustiveness :
    ∀ s ∈ evenBasis,
      s ∈ sector 0 0 ∨ s ∈ sector 2 0 ∨
      s ∈ sector 2 1 ∨ s ∈ sector 2 2 ∨
      s ∈ sector 4 2 ∨ s ∈ sector 4 3 := by
  native_decide

/-- The primitive SU(5) hypercharge weights of all six sectors. -/
theorem six_sector_hypercharges :
    (∀ s ∈ sector 0 0, chargeSix s = 0) ∧
    (∀ s ∈ sector 2 0, chargeSix s = 6) ∧
    (∀ s ∈ sector 2 1, chargeSix s = 1) ∧
    (∀ s ∈ sector 2 2, chargeSix s = -4) ∧
    (∀ s ∈ sector 4 2, chargeSix s = 2) ∧
    (∀ s ∈ sector 4 3, chargeSix s = -3) := by
  native_decide

/-- Full left-handed family has vanishing U(1)_Y-gravity anomaly.
The factor of six in the charge is irrelevant to vanishing. -/
theorem gravitational_hypercharge_anomaly :
    evenBasis.sum chargeSix = 0 := by
  native_decide

/-- Full left-handed family has vanishing cubic hypercharge anomaly.
This follows from actual exterior occupation weights, not a separately
entered list of Standard Model multiplet charges. -/
theorem cubic_hypercharge_anomaly :
    evenBasis.sum (fun s => (chargeSix s)^3) = 0 := by
  native_decide

/-- The primitive integral cocharacter is SU(5) trace-free. -/
theorem primitive_traceless :
    (3 : ℤ) * (-2) + 2 * 3 = 0 := by
  norm_num

/-- The six sector multiplicities exhaust the 16 complex Weyl slots. -/
theorem one_family_total :
    (1 : ℕ) + 1 + 6 + 3 + 3 + 2 = 16 := by
  norm_num

end GppSpinTenExteriorSpectrum

#print axioms GppSpinTenExteriorSpectrum.even_occupation_card
#print axioms GppSpinTenExteriorSpectrum.six_sector_counts
#print axioms GppSpinTenExteriorSpectrum.sector_exhaustiveness
#print axioms GppSpinTenExteriorSpectrum.six_sector_hypercharges
#print axioms GppSpinTenExteriorSpectrum.cubic_hypercharge_anomaly
