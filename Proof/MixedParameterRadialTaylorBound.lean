import Proof.Archive.MixedRadialJetCalculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma norm_parameterJetField_le (n : ℕ) (F : P × ℝ → V) (x : P × ℝ) :
    ‖parameterJetField n F x‖ ≤ ‖iteratedFDeriv ℝ n F x‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ P ℝ)

lemma norm_iteratedFDeriv_fixedDirectionalDerivative_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → V) (hF : ContDiff ℝ ∞ F) (v x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fixedDirectionalDerivative F v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (n+1) F x‖ := by
  have hD := (hF.fderiv_right (m:=∞) (by simp)).contDiffAt (x:=x)
  have hb := norm_iteratedFDeriv_clm_apply_const (c:=v) hD (n:=n) (by simp)
  change ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ F y v) x‖ ≤ _
  simpa only [norm_iteratedFDeriv_fderiv] using hb

lemma radialSecondDerivative_parameterJetField (n : ℕ) (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) :
    radialSecondDerivative (parameterJetField n F) = parameterJetField n (radialSecondDerivative F) := by
  change radialFirstDerivative (radialFirstDerivative (parameterJetField n F)) = _
  rw [radialFirstDerivative_parameterJetField n F hF,
    radialFirstDerivative_parameterJetField n (radialFirstDerivative F) (contDiff_radialFirstDerivative F hF)]
  rfl

lemma norm_radialSecond_parameterJetField_le (n : ℕ) (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) (x : P × ℝ) :
    ‖radialSecondDerivative (parameterJetField n F) x‖ ≤ ‖iteratedFDeriv ℝ (n+2) F x‖ := by
  rw [radialSecondDerivative_parameterJetField n F hF]
  have hRad : ‖((0:P),(1:ℝ))‖ = 1 := by simp
  have h1 := norm_iteratedFDeriv_fixedDirectionalDerivative_le F hF ((0:P),1) x (n+1)
  have h2 := norm_iteratedFDeriv_fixedDirectionalDerivative_le
    (fixedDirectionalDerivative F ((0:P),1)) (contDiff_fixedDirectionalDerivative F hF ((0:P),1)) ((0:P),1) x n
  rw [hRad,one_mul] at h1 h2
  exact (norm_parameterJetField_le n (radialSecondDerivative F) x).trans (h2.trans h1)

/-- Checked quantitative caller for every parameter jet of a quadratic
radial remainder. The budget B is explicit and must be supplied by the
actual geometry; no compactness bound for a single family is substituted
for uniformity over admitted metrics. -/
theorem norm_parameterJetField_quadratic_of_joint_bound
    (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) (s : Set P) (hs : IsOpen s)
    (hzero : ∀ p ∈ s,F (p,0) = 0)
    (hfirst : ∀ p ∈ s,HasDerivAt (fun r : ℝ => F (p,r)) 0 0)
    {p : P} (hp : p ∈ s) (n : ℕ) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hBound : ∀ t : ℝ,|t| ≤ δ → ‖iteratedFDeriv ℝ (n+2) F (p,t)‖ ≤ B)
    (r : ℝ) (hr : |r| ≤ δ) : ‖parameterJetField n F (p,r)‖ ≤ B*r^2 := by
  have hSlice : ContDiff ℝ ∞ (fun t : ℝ => parameterJetField n F (p,t)) :=
    (contDiff_parameterJetField n F hF).comp (contDiff_const.prodMk contDiff_id)
  have h0 := parameterJetField_zero_on_closure n F hF s hs hzero p (subset_closure hp)
  have hD0 := hasDerivAt_parameterJetField_zero_on_closure n F hF s hs hfirst p (subset_closure hp)
  have hDD (t : ℝ) (ht : |t| ≤ δ) :
      ‖deriv (deriv (fun u : ℝ => parameterJetField n F (p,u))) t‖ ≤ B := by
    rw [deriv_deriv_radialSlice (parameterJetField n F) (contDiff_parameterJetField n F hF) p t]
    exact (norm_radialSecond_parameterJetField_le n F hF (p,t)).trans (hBound t ht)
  have hTaylor := norm_sub_le_quadratic_of_second_deriv_le _ hSlice δ B hδ hB hD0 hDD r hr
  simpa only [h0,sub_zero] using hTaylor

end ShrinkingSpheres
