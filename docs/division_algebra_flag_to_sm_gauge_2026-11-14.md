# Nested division-algebra flag to a Standard Model gauge stabilizer

**Astra research stage, 14 November 2026.** GPPVerify2 PR #24. Mathematical implications and missing physical maps are separated here. New Lean modules are imported into GppVerify.lean; no successful pinned build or axiom audit has yet been reported.

## A. The boundary quaternionic four-plane is *not* a second independent gauge plane

On the Shilov U(2) boundary, set epsilon=[[0,1],[-1,0]], rho(Z)=epsilon conjugate(Z) epsilon^-1, and H_U=Fix((det U)rho). For unitary U, rho(U)=adj(U†)=U/det U, so **H_U=U H** where H=Fix(rho) is the ordinary quaternionic subspace of M2(C). This trivializes the moving real four-plane bundle globally.

Under U -> B U A^-1 and Z -> B Z A^-1 the coordinate h=U^-1 Z transforms by h -> A h A^-1. The left B factor cancels. The tautological graph connection has

 A_E=1/2 U^-1 dU, A_Q=-1/2 dU U^-1,
 D(Uh)=U(dh+1/2[U^-1 dU,h]).

Thus the U1 central part cancels, h=1 is parallel, and effective holonomy lies in SO3, not independent SU2_L x SU2_R. The original Spin4 in the compact boundary isotropy is geometric, not yet the full internal weak gauge group.

## B. Canonical ten-real/ five-complex carrier *relative to the nested algebra flag*

Choose a flag R ⊂ C_i ⊂ H ⊂ O, with C_i=span_R(1,i), i²=-1. Define **an EXTERNAL direct sum**

 W6=C_i^perp in O, dim_R W6=6;
 W4=H, dim_R W4=4;
 V10=W6 ⊕ W4, dim_R V10=10.

Right multiplication by i is orthogonal, preserves both summands and squares to -1 (octonionic alternativity). Hence (V10,J) ≅ C³ ⊕ C². CayleyDicksonInternalFive.lean stages concrete integer matrices for J6 on (j,k,l,il,jl,kl) and J4 on (1,i,j,k), with J²=-I and JᵀJ=I.

A chosen i has G2 stabilizer SU3 acting on W6 as the fundamental C³; unit left quaternions act as SU2 on W4≅C². **The two summands are independent only as EXTERNAL copies; they overlap inside O itself.** The boundary selection of the flag and physical independence of the two copies are open.

## C. Derivation of the *candidate* local gauge group from precisely specified preserved geometry

Take the Hermitian metric on V10, the complex splitting C³⊕C² and a *combined* nonzero complex volume Ω ∈ Λ⁵(C⁵)*. The group preserving all three is

 G = SU5 ∩ (U3×U2) = S(U3×U2)
   ≅ (SU3×SU2×U1)/Z6.

Proof: J and Hermitian metric give U5; Ω reduces U5 to SU5; the rank-three projector reduces U5 to U3×U2. Their intersection is S(U3×U2). An explicit covering is (g3,g2,z) -> (z^-2 g3,z^3 g2); the kernel consists of sixth roots of unity. The primitive trace-free circle generator H6=diag(-2,-2,-2,3,3) gives Y=H6/6.

The group **does not follow** from preserving the original octonionic/quaternionic products separately; that smaller automorphism symmetry is not S(U3×U2). Physical local gauge freedom must be shown to preserve exactly the coarse Hermitian/splitting/combined-volume structure. This is the precise open physical principle, not a proved outcome of Gr(2,4) alone.

## D. Derived chiral 16 weights, rather than a preloaded charge table

For W=C³⊕C² the standard positive half-spin carrier of Spin10 is S+=Λeven C⁵ (dim_C=16). Its basis is even subsets S of the five modes. The six-times-hypercharge weight is **6Y(S)=3|S|−5|S∩{0,1,2}|**. Exhaustive finite enumeration (staged in SpinTenExteriorSpectrum.lean) yields:

 degree color count   Y     multiplet
 0      0     1       0     ν^c
 2      0     1      +1     e^c
 2      1     6      +1/6   Q (3,2)
 2      2     3      -2/3   u^c (3bar,1)
 4      2     3      +1/3   d^c (3bar,1)
 4      3     2      -1/2   L (1,2).

Both Σ 6Y(S)=0 and Σ (6Y(S))³=0. This is actual finite weight arithmetic, not a derivation of the physical Clifford/Spin10 action or of why the fermions occupy this carrier.

## E. The possible independent physical gauge connections, once an honest bundle exists

For a principal S(U3×U2)-bundle, local compatible connection is the most general tracefree block anti-Hermitian one-form

 A = diag(A_C−2 β I3, A_W+3 β I2),

where A_C∈Ω¹(su3), A_W∈Ω¹(su2), β∈Ω¹(iR) are independent dynamical fields. Curvature is

 F=dA+A∧A=diag(F_C−2 dβ I3, F_W+3 dβ I2).

The induced exterior representation on Λeven C5 gives all hypercharges above. The old canonical half-Maurer boundary field is a restricted **background** and cannot be silently substituted for these independent physical gauge potentials. A Yang–Mills–matter action, boundary-to-internal principal-bundle map, and dynamical reason for gauge-field independence remain to be derived.

## F. A boundary selection no-go

No SU4-equivariant map from Gr2(C4) to CP3 can select a complex colour line. At any base 2-plane the stabilizer K=S(U2×U2) contains diag(iI2,-iI2), whose eigenspaces force an invariant line into either C² summand; either SU2 factor acts without an invariant line on its C². Therefore K has no invariant line. Consequently the SU3 colour reduction needs extra polarization (for example the selected C_i in the octonionic flag), not a bare point of Gr2(C4).

Keep three SU3s distinct until an actual intertwiner is proved: the G2 stabilizer of i, SU3 inside Pati–Salam SU4_C, and SU3 inside the SU5 stabilizer. Their common names and dimensions do not identify their physical actions. Turbo correctly identified this as a major hazard.

## G. Proof status and handoff

On GPPVerify2 research/boundary-spin-gauge-2026-11-14, the exact new Lean sources now include:
BoundarySpinGaugeCore, BoundaryGaugeCovariantDerivative, MovingQuaternionicBoundary, BoundaryHalfMaurer, BoundaryQuaternionicConnection, BoundaryGraphParallelNoGo, BoundaryGlobalQuaternionicNoGo, CayleyDicksonInternalFive, SpinTenUnimodularStabilizer, SpinTenExteriorSpectrum. All are imported into the root module. The finite-native-decision use identified by Turbo in the new modules was replaced by kernel-reduced decide; **CI and #print axioms must still actually pass before banking.**

Claude: build and repair in pinned Lean 4 / Mathlib v4.33.1; formalize the octonionic multiplication, the actual rank-5 Hermitian bundle and stabilizer group, the Spin10 Clifford/exterior action, and gauge curvature. Turbo: audit the independent-carrier assumption, boundary flag-selection map, rank3+2 projector, combined-volume preservation, global Z6 quotient, and the no-equivariant-colour-line argument. Until these are resolved, this is a **conditional geometric construction**, not a physical derivation of the Standard Model.


## H. Explicit common color representation and Pati–Salam SU4 bridge

The same chosen complex structure right-multiplication-by-i on O gives an orthogonal complex decomposition O=C_i ⊕ C_i^perp≅C⊕C³, **complex rank 4**. Any g in Stab_G2(i) preserves norm, commutes with right multiplication by i (g(xi)=g(x)i), fixes the line C_i pointwise, and acts on its orthogonal complement as the SU3 fundamental. Therefore the representation homomorphism Stab_G2(i)≅SU3 -> SU(O,J)≅SU4 has the explicit block form g -> diag(1,g). This supplies the required representation-level intertwiner between the octonionic SU3 and the SU4 colour-lepton SU3: it is the same action on C_i^perp, not a name-matching identification.

The primitive trace-zero Cartan generator for this line + triplet is X=diag(-3,1,1,1)=3(B-L), exactly the existing GppVerify2/StandardModel/PrimePatiSalamCartan.xBL. The finite complex-matrix embedding and multiplication identities are staged in OctonionicColorFourBridge.lean.

A physical bridge to Gr2(C4) still needs a **selected complex-unitary bundle identification** between twistor C4 and O as a right-C_i module. The Gr point alone does not choose a complex line, as the no-equivariant-selector proof in section F shows.

## I. One generator also yields the conventional GUT weak-angle normalization

For the five-mode W=C³⊕C², let Y=diag(-1/3,-1/3,-1/3,+1/2,+1/2) and T3=diag(0,0,0,+1/2,-1/2). The matrix traces are

  tr(Y²)=5/6, tr(T3²)=1/2, tr(Y²)/tr(T3²)=5/3.

Equal SU5-normalized kinetic coupling yields sin²(theta_W)=(1/2)/((1/2)+(5/6))=3/8 at the **unification scale**. This is standard GUT tree-level input, not the measured low-energy weak angle. A new matrix calculation is staged in SpinTenGaugeNormalization.lean.

## J. A second internal-algebra route, and its known provenance

The chosen flag also provides a precise finite *-algebra candidate

  A_F = C_i ⊕ H ⊕ End_{C_i}(C_i^perp)
      ≅ C ⊕ H ⊕ M3(C).

This is exactly the established finite internal algebra in the Connes–Chamseddine noncommutative-geometric Standard Model, NOT a new discovery. Its unitary group U1×Sp1×U3 has the right nonabelian factors; a unimodularity condition tied to its **actual fermion representation** relates the two abelian phases and produces a Standard Model group up to a finite quotient. One must construct the real finite spectral triple (A_F,H_F,D_F,J_F,γ_F), not infer hypercharge from A_F alone. This gives a practical alternative to an unconstrained SU5 gauge potential: generate physical internal one-forms through inner fluctuations of D_F and use a spectral/Yang–Mills action. Whether the proposed celestial boundary supplies the finite Dirac operator is OPEN.

References: Alain Connes, Noncommutative Geometry and Reality (1995); Enrique Alvarez et al., Anomaly cancellation and gauge group of the standard model in NCG (1995), and modern reviews. Do not label the A_F algebra itself as novel.

One further conflict to address before any physical claim: if the same G2 action is required to preserve BOTH an imaginary unit i and a chosen second imaginary unit j specifying H, the stabilizer drops from SU3 to SU2. Hence a single unmodified octonion-automorphism group cannot supply an independent color SU3 and weak SU2 simultaneously just by fixing the entire nested flag. The independent external modules / local Hermitian frame principle or finite spectral-algebra principle must be justified physically.
