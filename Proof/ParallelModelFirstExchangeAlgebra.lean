import Proof.ParallelModelFirstLeadingAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def modelFirstExchangeJetCorrection
    (RA BA : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (v w : SphereSobolev (3/2:ℝ)) (rv rw sv sw : SphereSobolev (1/2:ℝ)) : ℝ :=
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
  -(⟪Z (RA w),Z sv⟫_ℝ+⟪Z rw,Z (BA v)⟫_ℝ+⟪Z rw,Z sv⟫_ℝ)+
    (⟪Z (RA v),Z sw⟫_ℝ+⟪Z rv,Z (BA w)⟫_ℝ+⟪Z rv,Z sw⟫_ℝ)

/-- The mixed horizontal exchange is a Hodge density plus SIX genuine
first coefficient-jet products. Neither orientation is estimated alone. -/
lemma model_first_hodge_row_expansion
    (RA BA : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (v w : SphereSobolev (3/2:ℝ)) (rv rw sv sw : SphereSobolev (1/2:ℝ)) :
    let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    ⟪Z (RA w),Z (BA v)⟫_ℝ-⟪Z (RA v),Z (BA w)⟫_ℝ=
      (⟪Z (RA w+rw),Z (BA v+sv)⟫_ℝ-⟪Z (RA v+rv),Z (BA w+sw)⟫_ℝ)+
        modelFirstExchangeJetCorrection RA BA v w rv rw sv sw := by
  simp only [modelFirstExchangeJetCorrection,map_add,inner_add_left,inner_add_right]
  ring

lemma model_first_mass_products_le (u v β En : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hβ : 1 ≤ β) (hU : β*u^2 ≤ En) (hV : β⁻¹*v^2 ≤ En) :
    u^2 ≤ En ∧ v*u ≤ 2*En ∧ β⁻¹*(v*u) ≤ 2*En := by
  have hβp := zero_lt_one.trans_le hβ
  have hUV := weighted_product_le v u β hβp
  have hP : v*u ≤ 2*En := hUV.trans (by simpa only [two_mul] using add_le_add hV hU)
  have hU0 : u^2 ≤ En := (le_mul_of_one_le_left (sq_nonneg _) hβ).trans hU
  refine ⟨hU0,hP,?_⟩
  exact (mul_le_of_le_one_left (mul_nonneg hv hu) (inv_le_one_of_one_le₀ hβ)).trans hP

lemma model_first_hodge_jet_correction_bound
    (R B : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (RA BA : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hRA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp RA=
      R.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hBA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp BA=
      B.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (v w : SphereSobolev (3/2:ℝ)) (rv rw sv sw : SphereSobolev (1/2:ℝ))
    (R0 R1 B0 B1 ε β u En : ℝ)
    (hR0 : 0 ≤ R0) (hR1 : 0 ≤ R1) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hu : 0 ≤ u)
    (hR : ‖R‖ ≤ R0) (hB : ‖B‖ ≤ B0*ε/β)
    (hrv : ‖rv‖ ≤ R1*u) (hrw : ‖rw‖ ≤ R1*u)
    (hsv : ‖sv‖ ≤ B1*ε*u) (hsw : ‖sw‖ ≤ B1*ε*u)
    (hMass : β*u^2 ≤ En)
    (hv : β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖^2 ≤ En)
    (hw : β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) w‖^2 ≤ En) :
    |modelFirstExchangeJetCorrection RA BA v w rv rw sv sw| ≤
      (4*R0*B1+4*B0*R1+2*R1*B1)*ε*En := by
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hβp := zero_lt_one.trans_le hβ
  have hMR (t : SphereSobolev (3/2:ℝ)) (s : SphereSobolev (1/2:ℝ))
      (ht : β⁻¹*‖J t‖^2 ≤ En) (hs : ‖s‖ ≤ B1*ε*u) :
      |⟪Z (RA t),Z s⟫_ℝ| ≤ 2*R0*B1*ε*En := by
    have hPair := first_half_adjoint_pair_eq_physical_inner R.adjoint RA hRA t s
    rw [ContinuousLinearMap.adjoint_adjoint] at hPair
    rw [←hPair]
    have hp := (model_first_mass_products_le u ‖J t‖ β En hu (norm_nonneg _) hβ hMass ht).2.1
    calc
      _ ≤ ‖J t‖*‖R s‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖J t‖*(R0*(B1*ε*u)) := mul_le_mul_of_nonneg_left
        (((R.le_opNorm s).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))).trans
          (mul_le_mul_of_nonneg_left hs hR0)) (norm_nonneg _)
      _ = (R0*B1*ε)*(‖J t‖*u) := by ring
      _ ≤ (R0*B1*ε)*(2*En) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hMB (t : SphereSobolev (3/2:ℝ)) (r : SphereSobolev (1/2:ℝ))
      (ht : β⁻¹*‖J t‖^2 ≤ En) (hr : ‖r‖ ≤ R1*u) :
      |⟪Z r,Z (BA t)⟫_ℝ| ≤ 2*B0*R1*ε*En := by
    have hPair := first_half_adjoint_pair_eq_physical_inner B.adjoint BA hBA t r
    rw [ContinuousLinearMap.adjoint_adjoint] at hPair
    rw [real_inner_comm,←hPair]
    have hp := (model_first_mass_products_le u ‖J t‖ β En hu (norm_nonneg _) hβ hMass ht).2.2
    calc
      _ ≤ ‖J t‖*‖B r‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖J t‖*((B0*ε/β)*(R1*u)) := mul_le_mul_of_nonneg_left
        (((B.le_opNorm r).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))).trans
          (mul_le_mul_of_nonneg_left hr (by positivity))) (norm_nonneg _)
      _ = (B0*R1*ε)*(β⁻¹*(‖J t‖*u)) := by ring
      _ ≤ (B0*R1*ε)*(2*En) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hZZ (t : SphereSobolev (1/2:ℝ)) : ‖Z t‖ ≤ ‖t‖ := (Z.le_opNorm t).trans
    ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (one_mul _))
  have hRS (r s : SphereSobolev (1/2:ℝ)) (hr : ‖r‖ ≤ R1*u) (hs : ‖s‖ ≤ B1*ε*u) :
      |⟪Z r,Z s⟫_ℝ| ≤ R1*B1*ε*En := by
    calc
      _ ≤ ‖Z r‖*‖Z s‖ := abs_real_inner_le_norm _ _
      _ ≤ (R1*u)*(B1*ε*u) := mul_le_mul ((hZZ r).trans hr) ((hZZ s).trans hs) (norm_nonneg _) (by positivity)
      _ = (R1*B1*ε)*u^2 := by ring
      _ ≤ (R1*B1*ε)*En := mul_le_mul_of_nonneg_left
        (model_first_mass_products_le u ‖J v‖ β En hu (norm_nonneg _) hβ hMass hv).1 (by positivity)
  have hA := abs_add_le (⟪Z (RA w),Z sv⟫_ℝ+⟪Z rw,Z (BA v)⟫_ℝ) ⟪Z rw,Z sv⟫_ℝ
  have hA0 := abs_add_le ⟪Z (RA w),Z sv⟫_ℝ ⟪Z rw,Z (BA v)⟫_ℝ
  have hD := abs_add_le (⟪Z (RA v),Z sw⟫_ℝ+⟪Z rv,Z (BA w)⟫_ℝ) ⟪Z rv,Z sw⟫_ℝ
  have hD0 := abs_add_le ⟪Z (RA v),Z sw⟫_ℝ ⟪Z rv,Z (BA w)⟫_ℝ
  have hTotal := abs_add_le (-(⟪Z (RA w),Z sv⟫_ℝ+⟪Z rw,Z (BA v)⟫_ℝ+⟪Z rw,Z sv⟫_ℝ))
    (⟪Z (RA v),Z sw⟫_ℝ+⟪Z rv,Z (BA w)⟫_ℝ+⟪Z rv,Z sw⟫_ℝ)
  rw [abs_neg] at hTotal
  change |-(⟪Z (RA w),Z sv⟫_ℝ+⟪Z rw,Z (BA v)⟫_ℝ+⟪Z rw,Z sv⟫_ℝ)+
    (⟪Z (RA v),Z sw⟫_ℝ+⟪Z rv,Z (BA w)⟫_ℝ+⟪Z rv,Z sw⟫_ℝ)| ≤ _
  nlinarith only [hA,hA0,hD,hD0,hTotal,hMR w sv hw hsv,hMR v sw hv hsw,
    hMB v rw hv hrw,hMB w rv hw hrv,hRS rw sv hrw hsv,hRS rv sw hrv hsw]

end ShrinkingSpheres.ParallelEnergy
