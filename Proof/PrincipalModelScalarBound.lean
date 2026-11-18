import Proof.PrincipalModelScalarForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma degreeRaisingScalarCoefficients_weighted_bound (Q0 : SmoothCoefficientJets 2)
    (r : ℝ) (c b : I → ℝ) :
    (∑ a,taylorGeneratorWeight r a*‖degreeRaisingScalarCoefficients Q0 c b a‖) ≤
      firstErrorScalarFixedBudget Q0*((∑ i : I,|c i|)+8*(∑ i : I,|b i|)) := by
  let W := fun Q : TaylorGeneratorIndex → ClosedCoefficientJets 3 => ∑ a,taylorGeneratorWeight r a*‖Q a‖
  let J := firstErrorScalarFixedBudget Q0
  have hSmul (z : ℝ) (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) : W (z • Q)=|z| *W Q := by
    simpa only [W,Pi.smul_apply] using taylor_scalar_weighted_sum_smul r z Q
  have hSum (Q : I → TaylorGeneratorIndex → ClosedCoefficientJets 3) : W (∑ i : I,Q i) ≤ ∑ i : I,W (Q i) := by
    simpa only [W,Finset.sum_apply] using taylor_scalar_weighted_sum_finite_le r Q
  have hD : W (∑ i : I,c i • degreeScalarCoefficients Q0) ≤ J*(∑ i : I,|c i|) := by
    calc
      _ ≤ ∑ i : I,W (c i • degreeScalarCoefficients Q0) := hSum _
      _ ≤ ∑ i : I,|c i| *J := Finset.sum_le_sum (fun i _ => by
        rw [hSmul]
        exact mul_le_mul_of_nonneg_left (degreeScalarCoefficients_weighted_bound Q0 r) (abs_nonneg _))
      _ = _ := by rw [← Finset.sum_mul];ring
  have hR : W (∑ i : I,b i • flatRaisingScalarCoefficients Q0 i) ≤ (4*J)*(∑ i : I,|b i|) := by
    calc
      _ ≤ ∑ i : I,W (b i • flatRaisingScalarCoefficients Q0 i) := hSum _
      _ ≤ ∑ i : I,|b i| *(4*J) := Finset.sum_le_sum (fun i _ => by
        rw [hSmul]
        exact mul_le_mul_of_nonneg_left (flatRaisingScalarCoefficients_weighted_bound Q0 i r) (abs_nonneg _))
      _ = _ := by rw [← Finset.sum_mul];ring
  have hR2 : W ((2:ℝ) • (∑ i : I,b i • flatRaisingScalarCoefficients Q0 i)) ≤ 8*J*(∑ i : I,|b i|) := by
    rw [hSmul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
  have hAdd := taylor_scalar_weighted_sum_add_le r (∑ i : I,c i • degreeScalarCoefficients Q0)
    ((2:ℝ) • (∑ i : I,b i • flatRaisingScalarCoefficients Q0 i))
  exact hAdd.trans ((add_le_add hD hR2).trans_eq (by ring))

/-- The SAME model scalar coefficients have the actual epsilon/beta weight.
The estimate uses raw principal tensor bounds and the admitted radius bound. -/
lemma Admissible.principal_model_scalar_weighted_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (Q0 : SmoothCoefficientJets 2) {y : X} (hy : y ∈ Y) (j : I) :
    (∑ a,taylorGeneratorWeight (d.radius y) a*‖principalModelScalarCoefficients Q0 d y j a‖) ≤
      ((54*(K+1)*K^2+216*K^2)*firstErrorScalarFixedBudget Q0)*ε/beta d.γ d.radius y := by
  let β := beta d.γ d.radius y
  let r := d.radius y
  let J := firstErrorScalarFixedBudget Q0
  let B := 9*(K+1)*K^2
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let c : I → ℝ := fun i => (q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y
  let b : I → ℝ := fun i => q i j-(if i=j then 1 else 0)
  have hJ : 0 ≤ J := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hrβ : r*β ≤ 1 := ((radius_bounds r β floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.1).trans ((div_le_self hε hf).trans hε1)
  have hQ (i k : I) : |q i k| ≤ B := (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i k).2.1
  have hc (i : I) : |c i| ≤ 2*B*(ε/β) := by
    rw [show c i=(q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y from rfl,abs_mul]
    exact mul_le_mul ((abs_add_le _ _).trans ((add_le_add (hQ i j) (hQ j i)).trans_eq (by ring)))
      (hd.scaled_frame_logRadius_beta_small hf hy i) (abs_nonneg _) (by positivity)
  have hb (i : I) : |b i| ≤ 9*K^2*ε*r := (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).1
  have hcs : (∑ i : I,|c i|) ≤ 6*B*(ε/β) :=
    (Finset.sum_le_sum (fun i _ => hc i)).trans_eq (by simp only [Fin.sum_univ_three];ring)
  have hbs : (∑ i : I,|b i|) ≤ 27*K^2*ε*r :=
    (Finset.sum_le_sum (fun i _ => hb i)).trans_eq (by simp only [Fin.sum_univ_three];ring)
  have hW := (degreeRaisingScalarCoefficients_weighted_bound Q0 r c b).trans
    (mul_le_mul_of_nonneg_left (add_le_add hcs (mul_le_mul_of_nonneg_left hbs (by norm_num : (0:ℝ)≤8))) hJ)
  apply (le_div_iff₀ hβ).2
  calc
    _ ≤ (J*(6*B*(ε/β)+8*(27*K^2*ε*r)))*β := mul_le_mul_of_nonneg_right hW hβ.le
    _ = 6*B*J*ε+(216*J*K^2*ε)*(r*β) := by field_simp [hβ.ne'];ring
    _ ≤ 6*B*J*ε+216*J*K^2*ε := add_le_add le_rfl
      ((mul_le_mul_of_nonneg_left hrβ (by positivity : 0 ≤ 216*J*K^2*ε)).trans_eq (mul_one _))
    _ = _ := by dsimp only [B,J];ring
end ShrinkingSpheres
