import Proof.BilinearTaylorHigherJets
import Proof.WeakConormalTaylorIdentity
import Proof.CommonSupportWeakPoissonRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def conormalEnergyTaylorPostL (P0 : SphereSobolev (1/2:ℝ) →L[ℝ] H) :
    (SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ H) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ))
    (StrongDual ℝ (SphereSobolev (1/2:ℝ))) (SphereSobolev (-(1/2:ℝ)))
      (sphereSobolevDualRieszL (1/2:ℝ))).comp
    (sphereSurfaceMass⁻¹ • (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ))
      (StrongDual ℝ H) (StrongDual ℝ (SphereSobolev (1/2:ℝ)))
        ((ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) H ℝ).flip P0)))

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- The fixed testing map and Riesz normalization preserve every finite
    Taylor derivative of the genuine energy/Poisson product. -/
theorem norm_iteratedFDeriv_conormal_energy_taylor_le
    (E E1 : T → H →L[ℝ] StrongDual ℝ H) (E0 : H →L[ℝ] StrongDual ℝ H)
    (P P1 : T → SphereSobolev (1/2:ℝ) →L[ℝ] H)
    (P0 : SphereSobolev (1/2:ℝ) →L[ℝ] H) (x : T)
    (hE : ContDiffAt ℝ ∞ E x) (hE1 : ContDiffAt ℝ ∞ E1 x)
    (hP : ContDiffAt ℝ ∞ P x) (hP1 : ContDiffAt ℝ ∞ P1 x)
    (N : ℕ) (r CE CD CQE CQP CP1 : ℝ) (hr : 0 ≤ r)
    (hCE : 0 ≤ CE) (hCD : 0 ≤ CD) (hCQE : 0 ≤ CQE) (hCQP : 0 ≤ CQP) (hCP1 : 0 ≤ CP1)
    (hEJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j E x‖ ≤ CE)
    (hEDiff : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => E p-E0) x‖ ≤ CD*r)
    (hERem : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => E p-E0-r • E1 p) x‖ ≤ CQE*r^2)
    (hPRem : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => P p-P0-r • P1 p) x‖ ≤ CQP*r^2)
    (hP1Jets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j P1 x‖ ≤ CP1)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => (sphereSobolevDualRieszL (1/2:ℝ)).comp
      (sphereSurfaceMass⁻¹ • ((E p).bilinearComp (P p) P0-E0.bilinearComp P0 P0-
        r • (E0.bilinearComp (P1 p) P0+(E1 p).bilinearComp P0 P0)))) x‖ ≤
      ‖conormalEnergyTaylorPostL P0‖*
        bilinearTaylorJetBudget N (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) H (StrongDual ℝ H))
          CE CD CQE CQP CP1 P0*r^2 := by
  let R := fun p => (E p).comp (P p)-E0.comp P0-r • (E0.comp (P1 p)+(E1 p).comp P0)
  have hR : ContDiffAt ℝ ∞ R x := ((hE.clm_comp hP).sub contDiffAt_const).sub
    (((contDiffAt_const.clm_comp hP1).add (hE1.clm_comp contDiffAt_const)).const_smul r)
  have hBound := norm_iteratedFDeriv_bilinear_affine_remainder_le
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) H (StrongDual ℝ H))
    E E1 E0 P P1 P0 x hE hE1 hP hP1 N r CE CD CQE CQP CP1 hr hCE hCD hCQE hCQP hCP1
    hEJets hEDiff hERem hPRem hP1Jets n hn
  have hEq : (fun p => (sphereSobolevDualRieszL (1/2:ℝ)).comp
      (sphereSurfaceMass⁻¹ • ((E p).bilinearComp (P p) P0-E0.bilinearComp P0 P0-
        r • (E0.bilinearComp (P1 p) P0+(E1 p).bilinearComp P0 P0)))) =
      conormalEnergyTaylorPostL P0 ∘ R := by
    funext p
    apply ContinuousLinearMap.ext
    intro f
    apply congrArg (sphereSobolevDualRieszL (1/2:ℝ))
    apply ContinuousLinearMap.ext
    intro g
    rfl
  rw [hEq]
  exact (norm_iteratedFDeriv_clm_comp_le (conormalEnergyTaylorPostL P0) R x hR n).trans
    ((mul_le_mul_of_nonneg_left hBound (norm_nonneg _)).trans_eq (by ring))

end ShrinkingSpheres
