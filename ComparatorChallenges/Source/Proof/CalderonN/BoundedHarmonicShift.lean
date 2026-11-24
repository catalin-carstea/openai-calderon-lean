module

public import Proof.CalderonN.HarmonicDerivativeOperator
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
public import Proof.CalderonN.SmoothHarmonicWeights
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.GaussianSphere
public import Proof.CalderonN.HarmonicHilbertDecomposition
public import Proof.CalderonN.SphereHarmonicBridge

public section

/- The normalized angular shifts of the checked Proposition 5.3 proof,
   using its adjoint identity and the general-dimensional Hilbert sum. -/
noncomputable section
open scoped InnerProductSpace ENNReal

namespace CalderonN

open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

private abbrev HarmonicSequence (n : ℕ) [NeZero n] :=
  lp (fun k : ℕ => harmonicSphereSubspace n k) 2

private theorem lowerSequence_bound
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C)
    (u : HarmonicSequence n) (s : Finset ℕ) :
    (∑ k ∈ s, ‖A k (u (k+1))‖^2) ≤ (C * ‖u‖)^2 := sorry

private def lowerSequence
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C) (u : HarmonicSequence n) :
    HarmonicSequence n := by
  refine ⟨(fun k => A k (u (k+1))), memℓp_gen' (C := (C * ‖u‖)^2) ?_⟩
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lowerSequence_bound A hC hA u

private def lowerHarmonics
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C) : SphereL2 n →L[ℝ] SphereL2 n := by
  let e := sphereHarmonicDecomposition (n := n)
  let L : HarmonicSequence n →ₗ[ℝ] HarmonicSequence n := {
    toFun := lowerSequence A hC hA
    map_add' := by
      intro u v
      apply lp.ext
      funext k
      exact (A k).map_add (u (k+1)) (v (k+1))
    map_smul' := by
      intro c u
      apply lp.ext
      funext k
      exact (A k).map_smul c (u (k+1)) }
  let G := e.symm.toLinearEquiv.toLinearMap.comp (L.comp e.toLinearEquiv.toLinearMap)
  refine G.mkContinuous C (fun u => ?_)
  change ‖e.symm (lowerSequence A hC hA (e u))‖ ≤ C * ‖u‖
  rw [LinearIsometryEquiv.norm_map, ← e.norm_map u]
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (by positivity)
  intro s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  change (∑ k ∈ s, ‖A k (e u (k+1))‖^2) ≤ (C * ‖e u‖)^2
  exact lowerSequence_bound A hC hA (e u) s

private theorem norm_scaled_harmonicDerivative_le (m : ℕ) (i : I n)
    (q : ℝ) (hq : (m : ℝ) + 1 ≤ q) :
    ‖q⁻¹ • harmonicDerivative (sphereFischerInner n) m i‖ ≤ (n : ℝ) + 2 := sorry

/-- Lowering after undoing one Bessel weight in the input degree. -/
def normalizedLowering (i : I n) : SphereL2 n →L[ℝ] SphereL2 n :=
  lowerHarmonics (fun k => ((k : ℝ)+2)⁻¹ • harmonicDerivative (sphereFischerInner n) k i)
    (C := (n : ℝ)+2) (by positivity)
    (fun k => norm_scaled_harmonicDerivative_le k i _ (by linarith))

/-- Raising after undoing one Bessel weight in the input degree. -/
def normalizedRaising (i : I n) : SphereL2 n →L[ℝ] SphereL2 n :=
  ContinuousLinearMap.adjoint
    (lowerHarmonics (fun k => ((k : ℝ)+1)⁻¹ • harmonicDerivative (sphereFischerInner n) k i)
      (C := (n : ℝ)+2) (by positivity)
      (fun k => norm_scaled_harmonicDerivative_le k i _ le_rfl))

end CalderonN
