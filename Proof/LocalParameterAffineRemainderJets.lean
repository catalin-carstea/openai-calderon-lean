import Proof.LocalAffineRadialParameterTaylorBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

theorem iteratedFDeriv_parameter_affine_remainder_eq
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : P × ℝ → V) {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (r : ℝ) (hR : (p,r) ∈ U) (h0 : (p,0) ∈ U) (n : ℕ) :
    iteratedFDeriv ℝ n (fun q => F (q,r)-F (q,0)-r • radialFirstDerivative F (q,0)) p =
      parameterJetField n F (p,r)-parameterJetField n F (p,0)-
        r • parameterJetField n (radialFirstDerivative F) (p,0) := by
  have hFr : ContDiffAt ℝ ∞ (fun q => F (q,r)) p :=
    (hF.contDiffAt (hU.mem_nhds hR)).comp p (contDiffAt_id.prodMk contDiffAt_const)
  have hF0 : ContDiffAt ℝ ∞ (fun q => F (q,0)) p :=
    (hF.contDiffAt (hU.mem_nhds h0)).comp p (contDiffAt_id.prodMk contDiffAt_const)
  have hRad : ContDiffOn ℝ ∞ (radialFirstDerivative F) U :=
    (hF.fderiv_of_isOpen (m:=∞) hU (by simp)).clm_apply contDiffOn_const
  have hRad0 : ContDiffAt ℝ ∞ (fun q => radialFirstDerivative F (q,0)) p :=
    (hRad.contDiffAt (hU.mem_nhds h0)).comp p (contDiffAt_id.prodMk contDiffAt_const)
  change iteratedFDeriv ℝ n (((fun q => F (q,r))-(fun q => F (q,0)))-
    r • (fun q => radialFirstDerivative F (q,0))) p = _
  rw [iteratedFDeriv_sub_apply (f:=(fun q => F (q,r))-(fun q => F (q,0)))
      (g:=r • (fun q => radialFirstDerivative F (q,0))) ((hFr.sub hF0).of_le (by simp))
      ((contDiffAt_const.smul hRad0).of_le (by simp)),
    iteratedFDeriv_sub_apply (hFr.of_le (by simp)) (hF0.of_le (by simp)),
    iteratedFDeriv_const_smul_apply (hRad0.of_le (by simp)),
    ← parameterJetField_eq_iteratedFDeriv_of_open n F hU hF p r hR,
    ← parameterJetField_eq_iteratedFDeriv_of_open n F hU hF p 0 h0,
    ← parameterJetField_eq_iteratedFDeriv_of_open n _ hU hRad p 0 h0]

end ShrinkingSpheres
