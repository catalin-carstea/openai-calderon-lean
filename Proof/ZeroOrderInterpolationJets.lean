import Proof.ZeroOrderInterpolationFamily
import Proof.MidpointFamilyHigherJets
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma zeroOrderInterpolationFamily_finite_jets
    (KN : P → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (U : Set P) (hU : IsOpen U)
    (hc : ∀ p ∈ U,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (KH p)=
      (KN p).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (hKN : ContDiffOn ℝ ∞ KN U) (hKH : ContDiffOn ℝ ∞ KH U)
    (p0 : P) (hp0 : p0 ∈ U) (N : ℕ) (BN BH : ℝ)
    (hKNJ : SmoothFiniteJetBound KN p0 N BN) (hKHJ : SmoothFiniteJetBound KH p0 N BH) :
    SmoothFiniteJetBound (zeroOrderInterpolationFamily KN KH U hc) p0 N ((BN+BH)/2) := by
  let T := fun p => zeroOrderEndpointPair (KN p) (KH p)
  have hT (p : P) (hp : p ∈ U) : T p ∈ sphereSobolevCompatibleEndpoints :=
    zeroOrderEndpointPair_compatible (KN p) (KH p) (hc p hp)
  let RM := sphereSobolevCompatibleInterpolationFamily T U hT
  let L := fun p => (T p).1
  let H := fun p => (T p).2
  have hTS : ContDiffOn ℝ ∞ T U := (hKN.clm_comp contDiffOn_const).prodMk (hKH.clm_comp contDiffOn_const)
  have hRM : ContDiffAt ℝ ∞ RM p0 := (contDiffOn_sphereSobolevCompatibleInterpolationFamily T U hU hT hTS).contDiffAt (hU.mem_nhds hp0)
  have hL : ContDiffAt ℝ ∞ L p0 := hKNJ.smooth.clm_comp contDiffAt_const
  have hH : ContDiffAt ℝ ∞ H p0 := hKHJ.smooth.clm_comp contDiffAt_const
  have hLH : (fun p => (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp (H p)) =ᶠ[𝓝 p0]
      (fun p => (L p).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) := by
    filter_upwards [hU.mem_nhds hp0] with p hp
    exact hT p hp
  have hRH : (fun p => (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H p)) =ᶠ[𝓝 p0]
      (fun p => (RM p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) := by
    filter_upwards [hU.mem_nhds hp0] with p hp
    have hEq : RM p=sphereSobolevMidpointL (T p).1 (T p).2 (hT p hp) :=
      sphereSobolevCompatibleInterpolationFamily_of_mem T U hT p hp
    exact ((congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      A.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) hEq).trans
        (sphereSobolevMidpointL_inclusion _ _ _)).symm
  have hLo (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n L p0‖ ≤ BN :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le KN (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))) p0 hKNJ.smooth n).trans
      ((mul_le_mul (norm_sphereSobolevBesselOrderL_le _ _) (hKNJ.bound n hn) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hHi (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n H p0‖ ≤ BH :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le KH (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)) p0 hKHJ.smooth n).trans
      ((mul_le_mul (norm_sphereSobolevBesselOrderL_le _ _) (hKHJ.bound n hn) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hB := hKNJ.nonneg
  have hC := hKHJ.nonneg
  refine ⟨by positivity,(contDiffOn_zeroOrderInterpolationFamily KN KH U hU hc hKN hKH).contDiffAt (hU.mem_nhds hp0),?_⟩
  intro n hn
  have hm := norm_iteratedFDeriv_midpoint_family_le L H RM p0 hL hH hRM hLH hRH n BN BH hB hC (hLo n hn) (hHi n hn)
  exact (norm_iteratedFDeriv_operator_precomp_fixed_le RM (sphereSobolevBesselOrderL 0 1) p0 hRM n).trans
    ((mul_le_mul (norm_sphereSobolevBesselOrderL_le _ _) hm (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
end ShrinkingSpheres
