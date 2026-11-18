import Proof.HalfDegreeHigherLift
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres.SmoothFiniteJetBound
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma precomp_fixed {A : P → F →L[ℝ] G} {p : P} {N : ℕ} {B : ℝ}
    (hA : SmoothFiniteJetBound A p N B) (R : E →L[ℝ] F) :
    SmoothFiniteJetBound (fun x => (A x).comp R) p N (‖R‖*B) :=
  ⟨mul_nonneg (norm_nonneg _) hA.nonneg,hA.smooth.clm_comp contDiffAt_const,fun n hn =>
    (norm_iteratedFDeriv_operator_precomp_fixed_le A R p hA.smooth n).trans
      (mul_le_mul_of_nonneg_left (hA.bound n hn) (norm_nonneg _))⟩
lemma postcomp_fixed {A : P → E →L[ℝ] F} {p : P} {N : ℕ} {B : ℝ}
    (hA : SmoothFiniteJetBound A p N B) (L : F →L[ℝ] G) :
    SmoothFiniteJetBound (fun x => L.comp (A x)) p N (‖L‖*B) :=
  ⟨mul_nonneg (norm_nonneg _) hA.nonneg,contDiffAt_const.clm_comp hA.smooth,fun n hn =>
    (norm_iteratedFDeriv_operator_postcomp_fixed_le L A p hA.smooth n).trans
      (mul_le_mul_of_nonneg_left (hA.bound n hn) (norm_nonneg _))⟩
end ShrinkingSpheres.SmoothFiniteJetBound

namespace OAI.AnisotropicCalderon.SphereHarmonic
open ShrinkingSpheres
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma contDiffAt_halfDegreeHigherLift
    (R S : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (p : P)
    (hR : ContDiffAt ℝ ∞ R p) (hS : ContDiffAt ℝ ∞ S p) :
    ContDiffAt ℝ ∞ (fun x => halfDegreeHigherLift (R x) (S x)) p :=
  contDiffAt_const.clm_comp ((hR.clm_comp contDiffAt_const).add (hS.clm_comp contDiffAt_const))

lemma halfDegreeHigherLift_jet_bound
    {R S : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {p : P} {N : ℕ} {BR BS : ℝ}
    (hR : SmoothFiniteJetBound R p N BR) (hS : SmoothFiniteJetBound S p N BS) :
    SmoothFiniteJetBound (fun x => halfDegreeHigherLift (R x) (S x)) p N (BR+BS) := by
  have hh := ((hR.precomp_fixed (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))).add
    (hS.precomp_fixed (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))).postcomp_fixed
      (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ))
  have hBR := hR.nonneg
  have hBS := hS.nonneg
  have hBound : ‖sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)‖*
      (‖sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)‖*BR+
        ‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)‖*BS) ≤ BR+BS := by
    calc
      _ ≤ 1*(1*BR+1*BS) := by
        gcongr
        · exact norm_sphereSobolevBesselOrderL_le _ _
        · exact norm_sphereSobolevBesselOrderL_le _ _
        · exact norm_sphereSobolevInclusionL_le _ _ _
      _ = _ := by ring
  exact hh.weaken hBound
end OAI.AnisotropicCalderon.SphereHarmonic
