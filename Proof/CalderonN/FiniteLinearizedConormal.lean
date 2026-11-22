module

public import Proof.CalderonN.BallRotationConormal
public import Proof.CalderonN.FiniteHarmonicRotation
public import Proof.CalderonN.FiniteLinearizedBallCorrection
public import Proof.CalderonN.ActualConormalSobolevTaylor

import Mathlib.Tactic

/-! Weak angular commutator at the actual coefficient. Rotation of the
physical conormal response is tested using the exact derivative of the
bulk energy on the two harmonic replacements. -/

public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 3650000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon.SmoothSphereRotation BallDirichlet TauCeti PDE

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem abs_energy_variation_pair_le {U : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (E E₁ : U →L[ℝ] U →L[ℝ] ℝ) (b u c v : U) (r : ℝ) :
    |E b c-r*E₁ u v| ≤
      ‖E-r • E₁‖*‖u‖*‖v‖+‖E‖*‖b-u‖*‖c‖+‖E‖*‖u‖*‖c-v‖ := by
  have h : E b c-r*E₁ u v = (E-r • E₁) u v + E (b-u) c + E u (c-v) := by
    simp only [sub_apply,smul_apply,smul_eq_mul,map_sub]
    ring
  rw [h]
  simp only [← Real.norm_eq_abs]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add ((E-r • E₁).le_opNorm₂ _ _) (E.le_opNorm₂ _ _)) (E.le_opNorm₂ _ _))

private theorem sphere_integrable_of_continuous (u : X dim → ℝ) (hu : Continuous u) :
    Integrable (fun w : ↥(standardSphere dim) => u w) (sphereProbability dim) := by
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
  have h := (hu.comp continuous_subtype_val).continuousOn.integrableOn_compact
    (μ := sphereProbability dim) (isCompact_univ : IsCompact (univ : Set ↥(standardSphere dim)))
  simpa only [IntegrableOn,Measure.restrict_univ,Function.comp_def] using h

theorem uniform_finite_linearized_conormal (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    ∃ η H B : ℝ, 0 < η ∧ 0 ≤ H ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      ∃ A : X dim → Mat dim, ContDiff ℝ ∞ A ∧ EqOn A a (ball (0 : X dim) (5/4)) ∧
        (∀ z ∈ closedBall (0 : X dim) 1, (A z).PosDef) ∧
        ∀ (ellθ : X dim →L[ℝ] ℝ) (Aθ : X dim → Mat dim),
          ContDiff ℝ ∞ Aθ → ‖ellθ‖ ≤ 2*P →
          (∀ z ∈ ball (0 : X dim) 1, let R := Aθ-r • (fun z => ellθ z • (1 : Mat dim))
            ‖R z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ R z‖ ≤ Q*r^2) →
        ∀ f : HarmonicFiniteCoefficients dim,
          let u := harmonicFiniteSmooth f
          let qθ := harmonicFiniteDriftVariationSmooth ellθ f
          ∃ b w e E : SmoothData dim,
            EqOn b.1 u.1 (standardSphere dim) ∧ EqOn w.1 0 (standardSphere dim) ∧
            EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
            (∀ z ∈ ball (0 : X dim) 1,
              negativeBallDivergence a w.1 z = -negativeBallDivergence Aθ b.1 z) ∧
            (∀ z, e.1 z = w.1 z-r*qθ.1 z) ∧
            ‖smoothBallSobolev 2 e‖ ≤ H*r^2*‖smoothBallSobolev 2 u‖ ∧
            (∀ z, E.1 z = smoothBallConormal A w.1 z+smoothBallConormal Aθ b.1 z-
              r*(ellθ z*fderiv ℝ u.1 z z+fderiv ℝ qθ.1 z z)) ∧
            ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) E‖ ≤
              B*r^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
  obtain ⟨ηS,H,hηS,hH,hStrong⟩ := uniform_finite_linearized_ball_correction (Y := Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ P Q hP hQ
  obtain ⟨ηP,_,hηP,_,hPositive⟩ := uniform_normalized_coefficient_remainder_C2 (Y:=Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ 1 zero_le_one
  obtain ⟨ηW,C,hηW,hC,hWeak⟩ := uniform_actual_finite_weak_conormal_taylor (Y := Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  let σ := unitSphereArea dim
  let S := Real.sqrt σ
  let G := (dim : ℝ)^2*(Q+2*P)
  let D := (dim : ℝ)^2*Q
  let B := D*S*S+G*C*(S+C)+G*S*C
  have hσ : 0 < σ := unitSphereArea_pos
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨min (min ηS ηP) (min ηW 1),H,B/σ,
    lt_min (lt_min hηS hηP) (lt_min hηW zero_lt_one),hH,by positivity,?_⟩
  intro floor hf ε he hes d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
  obtain ⟨A,hA,hAa,hResp⟩ := hWeak floor hf ε he
    (hes.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy
  have hInc : ball (0 : X dim) 1 ⊆ ball (0 : X dim) (5/4) := ball_subset_ball (by norm_num)
  have hAc : EqOn A a (ball (0 : X dim) 1) := fun z hz => hAa (hInc hz)
  have hPos (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : (A z).PosDef := by
    rw [hAa ((closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4)) hz)]
    exact (hPositive floor hf ε he
      (hes.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy z hz).2.2.2.2
  obtain ⟨lo,hi,hUE⟩ := exists_uniformEllipticOn_fixedBall A hA.continuous hPos
  have hH (b : SmoothData dim) (hb : EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1)) :
      EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    have hGerm : A =ᶠ[𝓝 z] a := by
      filter_upwards [isOpen_ball.mem_nhds (hInc hz)] with w hw
      exact hAa hw
    rw [negativeBallDivergence_congr_germ hGerm (EventuallyEq.rfl (f := b.1))]
    exact hb hz
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have hr1 : r ≤ 1 := hrε.trans (hes.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨A,hA,hAa,hPos,?_⟩
  intro ellθ Aθ hAθ hEllθ hRemθ f
  let u := harmonicFiniteSmooth f
  let qθ := harmonicFiniteDriftVariationSmooth ellθ f
  let Fθ (z : X dim) := ellθ z • (1 : Mat dim)
  have hFθ : ContDiff ℝ ∞ Fθ := ellθ.contDiff.smul contDiff_const
  let T := fixedBallSmoothEnergyL hAθ.continuous
  let T₁ := fixedBallSmoothEnergyL hFθ.continuous
  have hRnorm : ‖T-r • T₁‖ ≤ D*r^2 := by
    have hc := norm_fixedBallSmoothEnergyL_le
      (hAθ.continuous.sub (hFθ.continuous.const_smul r)) (Q*r^2) (by positivity)
      (fun z hz k l => by
        rw [← Real.norm_eq_abs]
        exact (Matrix.norm_entry_le_entrywise_sup_norm _).trans (hRemθ z hz).1)
    rw [fixedBallSmoothEnergyL_sub hAθ.continuous (hFθ.continuous.const_smul r),
      fixedBallSmoothEnergyL_smul hFθ.continuous] at hc
    exact hc.trans_eq (by dsimp only [D]; ring)
  have hT1 : ‖T₁‖ ≤ (dim : ℝ)^2*(2*P) := by
    apply norm_fixedBallSmoothEnergyL_le hFθ.continuous (2*P) (by positivity)
    intro z hz k l
    have hE := hEllθ
    have hzN : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp (ball_subset_closedBall hz)
    have ht : |ellθ z| ≤ 2*P := (ellθ.le_opNorm z).trans
      ((mul_le_mul hE hzN (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
    change |ellθ z * (1 : Mat dim) k l| ≤ _
    rw [Matrix.one_apply]
    split_ifs
    · simpa only [mul_one] using ht
    · simp only [mul_zero,abs_zero]
      positivity
  have hT : ‖T‖ ≤ G*r := by
    conv_lhs => rw [show T = (T-r • T₁)+r • T₁ by abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    refine (add_le_add hRnorm (mul_le_mul_of_nonneg_left hT1 hr.le)).trans ?_
    have h := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ D*r by positivity)
    dsimp only [G,D] at h ⊢
    nlinarith only [h]
  have hU (g : HarmonicFiniteCoefficients dim) : ‖smoothSobolev (harmonicFiniteSmooth g)‖ ≤ S*‖L g‖ := by
    rw [← harmonicFirstOrderLift_finite_smooth g]
    exact norm_harmonicFirstOrderLift_le _
  obtain ⟨b,w,e,hbT,hwT,hbP,hwP,heEq,heNorm⟩ := hStrong floor hf ε he
    (hes.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy ellθ Aθ hAθ hEllθ hRemθ f
  obtain ⟨b₀,hb₀T,hb₀P,hb₀Norm,_⟩ := hResp f
  have hbEq := eqOn_closedUnitBall_of_equal_ball_forcing hA hUE hAc b b₀
    (fun z hz => (hbP hz).trans (hb₀P hz).symm) (fun z hz => (hbT hz).trans (hb₀T hz).symm)
  have hbNorm : ‖smoothSobolev b-smoothSobolev u‖ ≤ C*r*‖L f‖ := by
    rw [smoothSobolev_eq_of_eqOn_ball b b₀ (hbEq.mono ball_subset_closedBall)]
    exact hb₀Norm
  let U := smoothBallRadialDerivative u
  let Qθ := smoothBallRadialDerivative qθ
  let V : SmoothData dim := ⟨fun z => ellθ z*U.1 z+Qθ.1 z,(ellθ.contDiff.mul U.2).add Qθ.2⟩
  let base := smoothConormal A hA w
  let var := smoothConormal Aθ hAθ b
  let W : SmoothData dim := ⟨base.1+var.1,base.2.add var.2⟩
  let E : SmoothData dim := ⟨fun z => W.1 z-r*V.1 z,W.2.sub (contDiff_const.mul V.2)⟩
  refine ⟨b,w,e,E,hbT,hwT,hbP,hwP,heEq,heNorm,fun _ => rfl,?_⟩
  apply norm_smoothBoundarySobolev_le_of_finite_tests hn (1/2 : ℝ) (by norm_num) (by norm_num)
    E (B/σ*r^2*‖L f‖) (by positivity)
  intro g
  let v := harmonicFiniteSmooth g
  obtain ⟨c,hcT,hcP,hcNorm,_⟩ := hResp g
  have hcBound : ‖smoothSobolev c‖ ≤ (S+C)*‖L g‖ := by
    conv_lhs => rw [show smoothSobolev c = (smoothSobolev c-smoothSobolev v)+smoothSobolev v by abel]
    refine ((norm_add_le _ _).trans (add_le_add hcNorm (hU g))).trans ?_
    calc
      _ ≤ C*‖L g‖+S*‖L g‖ := by gcongr; exact (mul_le_mul_of_nonneg_left hr1 hC).trans_eq (mul_one _)
      _ = _ := by ring
  have hZero : EqOn (coordinateFluxDivergence (fun z =>
      smoothBallFlux A w.1 z+smoothBallFlux Aθ b.1 z)) 0 (ball (0 : X dim) 1) := by
    intro z hz
    have hAg : A =ᶠ[𝓝 z] a := by
      filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hAc hx
    have hEq := (negativeBallDivergence_congr_germ hAg (EventuallyEq.rfl (f := w.1))).trans (hwP z hz)
    change coordinateFluxDivergence (smoothBallFlux A w.1+smoothBallFlux Aθ b.1) z = 0
    rw [coordinateFluxDivergence_add ((contDiff_smoothBallFlux hA w).differentiable (by simp))
      ((contDiff_smoothBallFlux hAθ b).differentiable (by simp))]
    rw [coordinateFluxDivergence_smoothBallFlux,coordinateFluxDivergence_smoothBallFlux]
    linarith only [hEq]
  have hExact := integral_linearizedBallConormal hA hAθ
    (fun z hz => Matrix.isHermitian_iff_isSymm.mp (hPos z (ball_subset_closedBall hz)).isHermitian)
    b w c hwT hZero (hH c hcP)
  have hW : σ*(∫ w : ↥(standardSphere dim), v.1 w*W.1 w ∂(sphereProbability dim)) =
      T (smoothSobolev b) (smoothSobolev c) := by
    rw [fixedBallSmoothEnergyL_apply,← hExact]
    congr 1
    apply integral_congr_ae
    filter_upwards with w
    rw [hcT w.property,inner_add_right]
    rfl
  have hV : T₁ (smoothSobolev u) (smoothSobolev v) =
      σ*(∫ w : ↥(standardSphere dim), v.1 w*V.1 w ∂(sphereProbability dim)) := by
    rw [fixedBallSmoothEnergyL_apply]
    exact affineEnergy_harmonicFinite_eq_firstConormal ellθ f g
  have hSplit : σ*(∫ w : ↥(standardSphere dim), E.1 w*v.1 w ∂(sphereProbability dim)) =
      T (smoothSobolev b) (smoothSobolev c)-r*T₁ (smoothSobolev u) (smoothSobolev v) := by
    have hP (z : X dim) : E.1 z*v.1 z = v.1 z*W.1 z-r*(v.1 z*V.1 z) := by
      change (W.1 z-r*V.1 z)*v.1 z = _
      ring
    have hw := sphere_integrable_of_continuous _ (v.2.continuous.mul W.2.continuous)
    have hv := sphere_integrable_of_continuous _ (v.2.continuous.mul V.2.continuous)
    simp_rw [hP]
    have hInt : (∫ w : ↥(standardSphere dim), v.1 w*W.1 w-r*(v.1 w*V.1 w) ∂(sphereProbability dim)) =
        (∫ w : ↥(standardSphere dim), v.1 w*W.1 w ∂(sphereProbability dim)) -
        r*(∫ w : ↥(standardSphere dim), v.1 w*V.1 w ∂(sphereProbability dim)) := by
      exact (integral_sub hw (hv.const_mul r)).trans
        (congrArg (fun t => (∫ w : ↥(standardSphere dim), v.1 w*W.1 w ∂(sphereProbability dim))-t)
          (integral_const_mul r _))
    rw [hInt,hV,← hW]
    ring
  have hBnd := abs_energy_variation_pair_le T T₁
    (smoothSobolev b) (smoothSobolev u) (smoothSobolev c) (smoothSobolev v) r
  have hEstimate : |T (smoothSobolev b) (smoothSobolev c)-r*T₁ (smoothSobolev u) (smoothSobolev v)| ≤
      B*r^2*‖L f‖*‖L g‖ := by
    refine hBnd.trans ?_
    calc
      _ ≤ D*r^2*(S*‖L f‖)*(S*‖L g‖)+G*r*(C*r*‖L f‖)*((S+C)*‖L g‖)+
            G*r*(S*‖L f‖)*(C*r*‖L g‖) := by
        gcongr <;> first | exact hRnorm | exact hT | exact hU _ | exact hbNorm | exact hcNorm | exact hcBound
      _ = _ := by dsimp only [B]; ring
  rw [← hSplit,abs_mul,abs_of_pos hσ,mul_comm σ] at hEstimate
  apply (le_div_iff₀ hσ).mpr at hEstimate
  exact hEstimate.trans_eq (by ring)

end CalderonN
