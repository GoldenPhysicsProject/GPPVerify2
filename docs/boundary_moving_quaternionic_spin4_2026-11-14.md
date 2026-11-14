# Boundary determinant twist, Spin(4) connection and holonomy obstruction

Research result (Astra, 2026-11-14). **Not yet Lean/Mathlib CI-checked; do not bank as kernel-proved.** Detailed derivations are staged as new Lean modules in this draft PR, and handed to GPP-bridge PR #14 for Turbo/Claude audit.

## 1. Moving real 4-plane over the Shilov boundary

Use the matrix-ball Shilov boundary U(2), embedded in Gr(2,4) by the graph U -> Graph(U). On M_2(C) define ε = [[0,1],[-1,0]], ρ(Z)=ε bar(Z) ε^-1. It is an antilinear multiplicative involution, and Fix(ρ) consists of matrices [[a,b],[-bar(b),bar(a)]] ≅ H, dimension 4 over R.

A fixed copy of H is NOT invariant under K=S(U(2)×U(2)). Explicit K witness: A=diag(i,1), B=diag(-i,1), Z=I, giving Z'=BZA^-1=diag(-1,1), ρ(Z')=-Z' ≠ Z'.

**Exact rescue:** for d∈U(1) set κ_d=dρ, H_d=Fix(κ_d). Then κ_d²=1 and, locally choosing η²=d, H_d=ηH. Define d=det U at each U∈U(2). For U'=BUA^-1, d'=(det B/det A)d, and for unitary A,B,

    ρ(BZA^-1) = (det A/det B) Bρ(Z)A^-1
    κ_{d'}(BZA^-1) = Bκ_d(Z)A^-1.

Thus the moving H_d family is K-equivariant, unlike H_1. The real quadratic norm q_d(Z)=det Z/d≥0 on H_d is invariant.

The phase character χ(A,B)=det B/det A=(det A)^(-2) on K has phase stabilizer with identity component SU(2)×SU(2)≅Spin(4); the effective action on H_d is SO(4). The determinant fibration SU(2)≅S³ → U(2) → U(1)≅S¹ is the exact S³-over-S¹ boundary geometry.

## 2. Canonical connection from the Grassmannian graph

The graph and orthogonal-complement have normalized C⁴ frames

    V(U)=(I,U)^T / sqrt(2)
    W(U)=(-U†,I)^T / sqrt(2).

Their induced Hermitian connections are

    A_E=V† dV= 1/2 U^-1 dU = 1/2 θ
    A_Q=W† dW=-1/2 dU U^-1 = -1/2 α.

Maurer-Cartan identities dθ=-θ∧θ, dα=+α∧α give

    F_E=-1/4 θ∧θ; F_Q=-1/4 α∧α.

Both are nonzero in SU(2) directions. The 1/2 is fixed by frame normalization. On the round SU(2)≈S³ cylinder, θ/2 is the known homogeneous meron / sphaleron stationary Yang-Mills configuration, not a stable ground state (see JHEP 11 (2023) 146; https://d-nb.info/1238222307/34).

The Hom(E,Q) connection is D Z=dZ + A_Q Z - Z A_E. On a local determinant-phase patch U=e^{it}q, q∈SU(2), Z=e^{it}h, h∈H, this becomes

    D(e^{it}h)=e^{it}(dh - 1/2(dq q^-1)h - 1/2 h(q^-1 dq)).

It preserves the moving real quaternionic plane and is compatible with the two Spin(4) factors (they are not independent fields).

## 3. Strong holonomy no-go

The distinguished section Z=U∈H_det(U) is covariantly constant:

    D U=dU - 1/2(dU U^-1)U - 1/2 U(U^-1 dU)=0.

It has norm one in q_d. Thus holonomy of the induced SO(4) connection lies in SO(3), the stabilizer of the parallel section. **Canonical Grassmannian boundary projection alone does NOT yield independent SU(2)_L and SU(2)_R Yang-Mills fields.** To get those requires independent dynamical connection variables or a further mechanism, which cannot be presumed.

## 4. Different real forms and topology

At U=I, the Euclidean quaternionic plane is H=R I ⊕ su(2); the real tangent to the boundary is u(2)=iR I ⊕ su(2). They are *different* four-real-dimensional subspaces: the scalar time direction undergoes a Wick-type rotation. The Lie algebra u(2) maps to Hermitian Minkowski vectors via X↦-iX with signature (1,3), while det on H is positive.

On the full compact complex Gr(2,4), c1(TGr)=4H≠0 (rank-four complex tangent); a global real form would force c1 to be two-torsion and hence zero. So the moving real form should be constructed over the real Shilov boundary U(2), **not** claimed as a global real form of the complex tangent of the full Grassmannian. Coskun, *Grassmannians: The First Example of a Moduli Space*, https://homepages.math.uic.edu/~coskun/MITweek1.pdf.

## 5. Spin(10) bridge and independent-gauge-action gap

The existing SU(4) Plücker real 6-plane and the moving H_d real 4-plane give a candidate orthogonal real 10-plane bundle over U(2), with a possible Spin(10) structure. But the Spin(4) phase stabilizer is a **subgroup of the original SU(4)**, not yet an independent factor. Concluding independent SU(4)_C×SU(2)_L×SU(2)_R needs an actual joint principal-bundle action. Simply adding 6+4 and recognizing the correct abstract Spin groups would double-count the symmetry.

This remains open along with conformal SU(2,2) (beyond compact K) equivariance, dynamics, hypercharge/colour identification, and chiral 16 matter coupling.

## Staged files in this PR

- StandardModel/BoundarySpinGaugeCore.lean
- StandardModel/BoundaryGaugeCovariantDerivative.lean
- StandardModel/MovingQuaternionicBoundary.lean
- StandardModel/BoundaryHalfMaurer.lean
- StandardModel/BoundaryQuaternionicConnection.lean
- StandardModel/BoundaryGraphParallelNoGo.lean

**Claude:** run lake env lean on each under Mathlib v4.33.1, fix any tactic failures, assert #print axioms, add imports only after checks. **Turbo:** audit the K-equivariance, the SU(2) meron YM equation, the no-go and independent-action obstruction. Neither team should elevate geometric candidate to Standard Model derivation before those bridge maps exist.
