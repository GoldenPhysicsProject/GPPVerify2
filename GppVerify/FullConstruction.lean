import GppVerify

/-!
# GPPVerify full construction umbrella

`GppVerify.lean` is the historical root module.  During rapid research, a number of
proved modules were added behind focused CI lanes without immediately becoming imports
of that root.  This umbrella makes the current integration frontier import-connected.

The repository's ordinary `lake build` remains the stronger file-level compilation gate:
it builds the full `GppVerify` Lean library.  Building this module additionally checks
that the active proved construction can coexist in one import graph.
-/

-- Hadamard / Shadow-Euler finite algebra
import GppVerify.NumberTheory.HadamardShadowPairAlgebra
import GppVerify.NumberTheory.ShadowEulerFiniteCore

-- Principal-series / Riemann-celestial affine structure
import GppVerify.RiemannHypothesis.CelestialRiemannAffineBridge
import GppVerify.CelestialHolography.PositiveRealPrincipalSeries
import GppVerify.CelestialHolography.CompletedZetaPrincipalSeriesResponse

-- Grassmannian / orientation / zitterbewegung structure
import GppVerify.GrassmannianOrientationZ4

-- Prime Poisson / positive-type / causal heat arithmetic
import GppVerify.RiemannHypothesis.PrimePoissonRadialPositiveType
import GppVerify.RiemannHypothesis.FinitePrimePoissonRadialSum
import GppVerify.RiemannHypothesis.PositiveTypeLimit
import GppVerify.RiemannHypothesis.CosinePositiveType
import GppVerify.RiemannHypothesis.CausalHeatPrimePowerAnomaly
import GppVerify.RiemannHypothesis.CausalHeatVonMangoldtReindex
import GppVerify.RiemannHypothesis.FiniteHeatSemigroupGram
import GppVerify.RiemannHypothesis.FiniteHeatSemigroupMonotonicity
import GppVerify.RiemannHypothesis.LocalEulerShadowColligation

-- Prime-response transfer / arithmetic defect
import GppVerify.RiemannHypothesis.PrimeResponseContraction
import GppVerify.RiemannHypothesis.PrimeResponseTransferOperator

-- Exact sech / Wiener-Hopf / Gamma chamber structure
import GppVerify.RiemannHypothesis.SechSixthIntegral
import GppVerify.CelestialHolography.WienerHopfGammaChamberPositiveFactor

-- Scalar-box regulator and physical convergence
import GppVerify.CelestialHolography.ScalarBoxRegulatorAlgebra
import GppVerify.CelestialHolography.PositiveRegulatorEventuallySmall
import GppVerify.CelestialHolography.ScalarBoxAutomaticRegulatorConvergence

-- D-dimensional / massive celestial cut closure
import GppVerify.CelestialHolography.MassiveVectorPhysicalChartClosure
import GppVerify.CelestialHolography.MassiveCutRadialMu4Weight
import GppVerify.CelestialHolography.MassiveCutMu4RadialMoment
import GppVerify.CelestialHolography.TwoFlowScalarStateSum

-- Quantum-information / Standard-Model finite cores
import GppVerify.StandardModel.UniversalNotFidelity

-- This declaration provides a stable CI target for the import-connected construction.
theorem fullConstruction_loaded : True := trivial

#print axioms fullConstruction_loaded
