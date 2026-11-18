import Proof.SharpMultiplierForcingBound
import Proof.HalfRadialMultiplierCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

lemma norm_gradient_real_mul_le (f g : X → ℝ) (z : X)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    ‖gradient (fun w => f w*g w) z‖ ≤ |f z| *‖gradient g z‖+|g z| *‖gradient f z‖ := by
  rw [TauCeti.norm_gradient_eq_norm_fderiv,fderiv_fun_mul hf hg]
  calc
    _ ≤ ‖f z • fderiv ℝ g z‖+‖g z • fderiv ℝ f z‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        ← (TauCeti.norm_gradient_eq_norm_fderiv (𝕜:=ℝ) g z),← (TauCeti.norm_gradient_eq_norm_fderiv (𝕜:=ℝ) f z)]

/-- The SAME native bulk multiplier forcing is bounded by the actual local
matrix C1 size and the multiplier's first two spatial jets. -/
theorem norm_nativeBulkMultiplierForcing_local_C1 (F : SmoothCoefficientMatrix 2)
    (Q : SmoothCoefficientJets 3) (q B : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hF0 : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) z| ≤ q)
    (hF1 : ∀ i j,∀ z ∈ (ballOpens:Set X),‖gradient (coefficientValue 2 (F i j)) z‖ ≤ q)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B) :
    ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q‖ ≤
      (15*nativeMultiplierForcingGradientBudget*B)*q := by
  let C := smoothMultiplierColumnJets F Q
  let R := smoothMultiplierRowJets F Q
  let d := smoothMultiplierDriftJets (fun _ : I => (0:SmoothCoefficientJets 1)) Q
  have hVal (i j : I) (z : X) (hz : z ∈ (ballOpens:Set X)) :
      |coefficientValue 2 (F i j) z*(gradient (coefficientValue 3 Q) z) j| ≤ q*B := by
    rw [abs_mul]
    exact mul_le_mul (hF0 i j z hz) (hQ1 j z hz) (abs_nonneg _) hq
  have hC0 (i : I) (z : X) (hz : z ∈ (ballOpens:Set X)) : |coefficientValue 2 (C i) z| ≤ 6*q*B := by
    rw [coefficientValue_smoothMultiplierColumnJets]
    have h := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun j _ => hVal i j z hz))
    have hSum : (∑ _j : I,q*B) ≤ 6*q*B := by simp only [Fin.sum_univ_three];nlinarith [mul_nonneg hq hB]
    exact h.trans hSum
  have hR (j : I) (z : X) (hz : z ∈ (ballOpens:Set X)) : |coefficientValue 1 (R j) z| ≤ 3*q*B := by
    rw [coefficientValue_smoothMultiplierRowJets]
    exact ((Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun i _ =>
      (abs_mul _ _).le.trans (mul_le_mul (hF0 i j z hz) (hQ1 i z hz) (abs_nonneg _) hq)))).trans_eq
        (by simp only [Fin.sum_univ_three];ring)
  have hC1 (i : I) (z : X) (hz : z ∈ (ballOpens:Set X)) : ‖gradient (coefficientValue 2 (C i)) z‖ ≤ 6*q*B := by
    let t := fun (j : I) (w : X) => coefficientValue 2 (F i j) w*(gradient (coefficientValue 3 Q) w) j
    have hDiff (j : I) : DifferentiableAt ℝ (t j) z :=
      ((contDiff_coefficientValue 2 (F i j)).differentiable (by simp) z).mul
        ((contDiff_multiplier_gradient_coordinate Q j).differentiable (by simp) z)
    have hTerm (j : I) : ‖fderiv ℝ (t j) z‖ ≤ 2*q*B := by
      rw [← TauCeti.norm_gradient_eq_norm_fderiv]
      have h := norm_gradient_real_mul_le (coefficientValue 2 (F i j))
        (fun w => (gradient (coefficientValue 3 Q) w) j) z
        ((contDiff_coefficientValue 2 (F i j)).differentiable (by simp) z)
        ((contDiff_multiplier_gradient_coordinate Q j).differentiable (by simp) z)
      exact h.trans ((add_le_add (mul_le_mul (hF0 i j z hz) (hQ2 j z hz) (norm_nonneg _) hq)
        (mul_le_mul (hQ1 j z hz) (hF1 i j z hz) (norm_nonneg _) hB)).trans_eq (by ring))
    have hFun : coefficientValue 2 (C i) = (t 0+t 1)+t 2 := by
      rw [coefficientValue_smoothMultiplierColumnJets]
      funext w
      simp only [Fin.sum_univ_three,Pi.add_apply]
      rfl
    rw [hFun,TauCeti.norm_gradient_eq_norm_fderiv,
      fderiv_add ((hDiff 0).add (hDiff 1)) (hDiff 2),fderiv_add (hDiff 0) (hDiff 1)]
    exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
      ((add_le_add (add_le_add (hTerm 0) (hTerm 1)) (hTerm 2)).trans_eq (by ring))
  have hd (z : X) (_hz : z ∈ (ballOpens:Set X)) : |coefficientValue 1 d z| ≤ 0 := by
    rw [coefficientValue_smoothMultiplierDriftJets]
    change |∑ i : I,(0:ℝ)*(gradient (coefficientValue 3 Q) z) i| ≤ 0
    simp
  have h := norm_nativeSmoothMultiplierForcingL_local_C1 fixedSobolevCalculus C R d
    (6*q*B) (3*q*B) 0 (by positivity) (by positivity) (by norm_num) hC0 hC1 hR hd
  have hBound : ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q‖ ≤
      (2*(6*q*B)+3*q*B)*nativeMultiplierForcingGradientBudget := by
    simpa only [nativeBulkMultiplierCommutatorForcingL,C,R,d,zero_mul,add_zero] using h
  exact hBound.trans_eq (by ring)


/-- The gained actual boundary commutator uses only local coefficient C1
and multiplier two-jet budgets, plus the SAME native inverse/weak lift. -/
theorem norm_halfRadialMultiplierCommutator_local_C1 (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) (q B : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hF0 : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) z| ≤ q)
    (hF1 : ∀ i j,∀ z ∈ (ballOpens:Set X),‖gradient (coefficientValue 2 (F i j)) z‖ ≤ q)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B) :
    ‖halfRadialMultiplierCommutatorL F ha Q‖ ≤
      ‖fixedHalfOutwardTraceL‖*‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖*
        ((15*nativeMultiplierForcingGradientBudget*B)*q)*
        ‖nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner‖+
      ‖nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace Q‖ := by
  have hForce := norm_nativeBulkMultiplierForcing_local_C1 F Q q B hq hB hF0 hF1 hQ1 hQ2
  apply (norm_halfRadialMultiplierCommutatorL_le F ha Q).trans
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hForce (mul_nonneg (norm_nonneg fixedHalfOutwardTraceL)
      (norm_nonneg (strongDirichletOperator fixedSobolevCalculus 0 F).inverse))) (norm_nonneg _)

end ShrinkingSpheres
