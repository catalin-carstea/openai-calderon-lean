import Proof.NormalFrameRelativeGeometry
import Proof.PositiveAffineFamilyJets
import Proof.PositiveJetCompositionBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def normalFrameRelativeRadiusLinearL (r : ℝ) :
    (NormalFrameSpatialParameter × ℝ) →L[ℝ] (NormalFrameSpatialParameter × ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).prod (r • ContinuousLinearMap.snd ℝ _ _)

lemma norm_normalFrameRelativeRadiusLinearL_le_one (r : ℝ) (hr : |r| ≤ 1) :
    ‖normalFrameRelativeRadiusLinearL r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖(q.1,r • q.2)‖ ≤ 1*‖q‖
  have h1 : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
  have h2 : ‖r • q.2‖ ≤ ‖q‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
      (by simpa only [one_mul] using norm_snd_le q)
  simpa only [Prod.norm_def,one_mul] using max_le h1 h2

def normalFrameRelativeRadiusInput (r : ℝ) (q : NormalFrameRelativeParameter × X) :
    NormalFrameSpatialParameter × ℝ :=
  ((q.1.1,q.2),(1+q.1.2)*r)

lemma normalFrameRelativeRadiusInput_affine (r : ℝ) :
    normalFrameRelativeRadiusInput r = fun q =>
      ((0:NormalFrameSpatialParameter),r)+
        (normalFrameRelativeRadiusLinearL r).comp normalFrameRelativeReorderL q := by
  funext q
  simp only [normalFrameRelativeRadiusInput,normalFrameRelativeRadiusLinearL,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    smul_apply,Prod.mk_add_mk,zero_add,smul_eq_mul]
  change ((q.1.1,q.2),(1+q.1.2)*r) = ((q.1.1,q.2),r+r*q.1.2)
  congr 1
  ring

lemma contDiff_normalFrameRelativeRadiusInput (r : ℝ) : ContDiff ℝ ∞ (normalFrameRelativeRadiusInput r) := by
  rw [normalFrameRelativeRadiusInput_affine]
  exact contDiff_const.add ((normalFrameRelativeRadiusLinearL r).comp normalFrameRelativeReorderL).contDiff

lemma norm_iteratedFDeriv_normalFrameRelativeRadiusInput_le_one
    (r : ℝ) (hr : |r| ≤ 1) (q : NormalFrameRelativeParameter × X) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (normalFrameRelativeRadiusInput r) q‖ ≤ 1 := by
  let L := (normalFrameRelativeRadiusLinearL r).comp normalFrameRelativeReorderL
  have hProduct : ‖normalFrameRelativeRadiusLinearL r‖*‖normalFrameRelativeReorderL‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (norm_normalFrameRelativeRadiusLinearL_le_one r hr)
      (norm_nonneg normalFrameRelativeReorderL)).trans
        (by simpa only [one_mul] using norm_normalFrameRelativeReorderL_le_one)
  have hL : ‖L‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans hProduct
  rw [normalFrameRelativeRadiusInput_affine,iteratedFDeriv_fixed_add_positive _ _ q n hn]
  exact norm_iteratedFDeriv_clm_le_one L hL q n hn

/-- Uniform genuine radial coefficient jets transfer to the joint
    center/frame/relative-radius/spatial input with a fixed finite-order cost. -/
theorem norm_iteratedFDeriv_relative_coefficient_of_joint_bound
    (F : NormalFrameSpatialParameter × ℝ → Mat) (p : X × (X →L[ℝ] X)) (z : X)
    (r : ℝ) (hr : |r| ≤ 1) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ContDiffAt ℝ ∞ F ((p,z),r))
    (hJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j F ((p,z),r)‖ ≤ B)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (F ∘ normalFrameRelativeRadiusInput r) ((p,0),z)‖ ≤ (N.factorial:ℝ)*B := by
  have hInput : normalFrameRelativeRadiusInput r ((p,0),z) = ((p,z),r) := by
    simp only [normalFrameRelativeRadiusInput,add_zero,one_mul]
  have hAt : ContDiffAt ℝ ∞ F (normalFrameRelativeRadiusInput r ((p,0),z)) := by rwa [hInput]
  have hOut (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j F (normalFrameRelativeRadiusInput r ((p,0),z))‖ ≤ B := by
    rw [hInput]
    exact hJets j hj
  have hh := iteratedFDeriv_comp_common_bound (normalFrameRelativeRadiusInput r) F ((p,0),z)
    (contDiff_normalFrameRelativeRadiusInput r).contDiffAt hAt N B 1 hB le_rfl hOut
    (fun j hj _ => norm_iteratedFDeriv_normalFrameRelativeRadiusInput_le_one r hr _ j hj) n hn
  simpa only [one_pow,mul_one] using hh

end ShrinkingSpheres
