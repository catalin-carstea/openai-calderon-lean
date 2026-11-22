module

public import Proof.CalderonN.AngularPoissonEquation
public import Proof.CalderonN.ActualAngularCoefficientJets
public import Proof.CalderonN.FiniteHarmonicRotation
public import Proof.CalderonN.NormalizedStrongPoissonTaylor

import Mathlib.Tactic

/-! The strong angular correction uses the same physical Dirichlet
problem and the same polynomial first variation as the conormal estimate. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 5550000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private def smoothDivergenceData (a : X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (u : SmoothData dim) : SmoothData dim :=
  ⟨negativeBallDivergence a u.1,contDiff_negativeBallDivergence ha u.2⟩

private def smoothDifference (u v : SmoothData dim) : SmoothData dim := ⟨u.1-v.1,u.2.sub v.2⟩

private def smoothScale (r : ℝ) (u : SmoothData dim) : SmoothData dim := ⟨r • u.1,u.2.const_smul r⟩

private theorem smoothBallSobolev_difference (k : ℕ) (u v : SmoothData dim) :
    smoothBallSobolev k (smoothDifference u v) = smoothBallSobolev k u-smoothBallSobolev k v :=
  map_sub (smoothBallSobolevLinear dim k) (⟨u.1,u.2⟩ : smoothBallDataSubmodule dim) ⟨v.1,v.2⟩

private theorem smoothBallSobolev_scale (k : ℕ) (r : ℝ) (u : SmoothData dim) :
    smoothBallSobolev k (smoothScale r u) = r • smoothBallSobolev k u :=
  map_smul (smoothBallSobolevLinear dim k) r (⟨u.1,u.2⟩ : smoothBallDataSubmodule dim)

private theorem norm_affine_identity_matrix_jets_le (ell : X dim →L[ℝ] ℝ) {z : X dim}
    (hz : ‖z‖ ≤ 1) :
    ‖ell z • (1 : Mat dim)‖ ≤ ‖ell‖ ∧
      ‖fderiv ℝ (fun x => ell x • (1 : Mat dim)) z‖ ≤ ‖ell‖ := by
  let L := ell.smulRight (1 : Mat dim)
  constructor
  · rw [norm_smul,norm_one,mul_one]
    exact (ell.le_opNorm z).trans ((mul_le_of_le_one_right (norm_nonneg _) hz))
  · change ‖fderiv ℝ (⇑L) z‖ ≤ _
    rw [ContinuousLinearMap.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [ContinuousLinearMap.smulRight_apply,norm_smul,norm_one,mul_one]
    exact ell.le_opNorm x

/-- The genuine angular commutator, after subtracting its first
polynomial correction, is quadratic in the native bulk H2 norm. -/
theorem uniform_actual_strong_angular_correction (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      ∀ i j : Fin dim, ∀ f : HarmonicFiniteCoefficients dim,
        let u := harmonicFiniteSmooth f
        let ellθ := ell.comp (ballRotationGeneratorL i j)
        let qθ := harmonicFiniteDriftVariationSmooth ellθ f
        ∃ b bθ e : SmoothData dim,
          EqOn b.1 u.1 (standardSphere dim) ∧
          EqOn bθ.1 (sphereRotationDerivative i j u.1) (standardSphere dim) ∧
          EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
          EqOn (negativeBallDivergence a bθ.1) 0 (ball (0 : X dim) 1) ∧
          (∀ z, e.1 z = (angularBallCorrection i j b bθ).1 z-r*qθ.1 z) ∧
          ‖smoothBallSobolev 2 e‖ ≤ B*r^2*‖smoothBallSobolev 2 u‖ := by
  obtain ⟨η,P,Q,hη,hP,hQ,hLifts⟩ := uniform_normalized_coefficient_lifts (Y := Y)
    hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηθ,Pθ,Qθ,hηθ,hPθ,hQθ,hJets⟩ := uniform_actual_angular_coefficient_jets (Y := Y)
    hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨F0,hF0,δ,C,hδ,hC,hInv⟩ := exists_uniform_strongDirichlet_neighborhood dim 0
  let S := fullC1OperatorBudget (dim := dim)
  let D := ‖fullBallCoefficientOperatorL dim 0‖*(P+Q)
  let G := S*(Qθ+2*Pθ)
  let B := C*(G*(C*D)+S*Qθ+D*(C*(S*(2*Pθ))))
  let τ := min (min η ηθ) (min 1 (δ/(P+Q+1)))
  have hS : 0 ≤ S := fullC1OperatorBudget_nonneg
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨τ,B,lt_min (lt_min hη hηθ) (lt_min zero_lt_one (div_pos hδ (by positivity))),hB,?_⟩
  intro floor hf ε he hes d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  obtain ⟨F,F1,hF,_,hFn1,hFnR,lo,hi,hEll⟩ := hLifts F0 hF0 floor hf ε he
    (hes.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  let A := coefficientMatrixField 2 F
  let A0 := coefficientMatrixField 2 F0
  let AF := coefficientMatrixField 2 (F-F0)
  let I : X dim → Mat dim := fun _ => 1
  have ha := contDiff_coefficientMatrixField 2 F
  have hA0 := contDiff_coefficientMatrixField 2 F0
  have hAF := contDiff_coefficientMatrixField 2 (F-F0)
  have hAFEq : AF = A-A0 := by
    funext x
    ext k l
    unfold AF A A0 coefficientMatrixField coefficientValue
    rfl
  have hA0Germ (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A0 =ᶠ[𝓝 z] I := by
    have hz' := ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz
    filter_upwards [isOpen_ball.mem_nhds hz'] with w hw using hF0 w (ball_subset_closedBall hw)
  have hAgerm (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] a := by
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5/4) hz)]
      with w hw using hF hw
  have hF0Ell : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A0 1 1 := by
    have h0 := uniformlyEllipticOn_const_one_one (n := Fin dim) (fixedBallOpens dim : Set (X dim))
    refine ⟨h0.1,h0.2.1,fun z hz => ?_⟩
    rw [show A0 z = 1 from (hA0Germ z hz).eq_of_nhds]
    exact h0.2.2 hz
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have hr1 : r ≤ 1 := hrε.trans (hes.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hNear : ‖F-F0‖ ≤ (P+Q)*r := by
    conv_lhs => rw [show F-F0 = (F-F0-r • F1)+r • F1 by abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    refine (add_le_add hFnR (mul_le_mul_of_nonneg_left hFn1 hr.le)).trans ?_
    have hh := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ Q*r by positivity)
    nlinarith only [hh]
  have hInvA : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C := by
    apply hInv F lo hi _ hEll
    have hR := hrε.trans (hes.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hh := (le_div_iff₀ (show 0 < P+Q+1 by positivity)).mp hR
    exact hNear.trans (by nlinarith only [hh,hr])
  have hInv0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ C :=
    hInv F0 1 1 (by rw [sub_self,norm_zero]; exact hδ.le) hF0Ell
  have hAFNorm (u : SmoothData dim) : ‖smoothBallSobolev 0 (smoothDivergenceData AF hAF u)‖ ≤
      D*r*‖smoothBallSobolev 2 u‖ := by
    obtain ⟨hs,hh⟩ := fullBallDivergence_native_smooth 0 (F-F0) u
    change fullBallDivergenceL 0 (F-F0) (smoothBallSobolev 2 u) =
      smoothBallSobolev 0 (smoothDivergenceData AF hAF u) at hh
    rw [← hh,← fullBallCoefficientOperatorL_apply]
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact ((fullBallCoefficientOperatorL dim 0).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left hNear (norm_nonneg _)).trans_eq (by dsimp only [D]; ring))
  intro i j f
  let u := harmonicFiniteSmooth f
  let ellθ := ell.comp (ballRotationGeneratorL i j)
  let qθ := harmonicFiniteDriftVariationSmooth ellθ f
  let fθ := finiteHarmonicRotationL i j f
  let Aθ := ballRotationCoefficient i j A
  let Lθ (z : X dim) := ellθ z • (1 : Mat dim)
  let Rθ := Aθ-r • Lθ
  let hAθ := contDiff_ballRotationCoefficient i j ha
  let hLθ : ContDiff ℝ ∞ Lθ := ellθ.contDiff.smul contDiff_const
  let hRθ : ContDiff ℝ ∞ Rθ := hAθ.sub (hLθ.const_smul r)
  have hθ := ((hJets floor hf ε he
    (hes.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy).2 A ha hF).2 i j
  have hLocL (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      ‖Lθ z‖ ≤ 2*Pθ ∧ ‖fderiv ℝ Lθ z‖ ≤ 2*Pθ :=
    let h := norm_affine_identity_matrix_jets_le ellθ (mem_closedBall_zero_iff.mp (ball_subset_closedBall hz))
    ⟨h.1.trans hθ.1,h.2.trans hθ.1⟩
  have hLocR (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      ‖Rθ z‖ ≤ Qθ*r^2 ∧ ‖fderiv ℝ Rθ z‖ ≤ Qθ*r^2 := hθ.2 z (ball_subset_closedBall hz)
  have hLocA (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      ‖Aθ z‖ ≤ (Qθ+2*Pθ)*r ∧ ‖fderiv ℝ Aθ z‖ ≤ (Qθ+2*Pθ)*r := by
    have hRem := hLocR z hz
    have hLin := hLocL z hz
    have hExpr : Aθ = Rθ+r • Lθ := by dsimp only [Rθ]; abel
    have hExpr' := congrFun hExpr z
    have hDExpr : fderiv ℝ Aθ z = fderiv ℝ Rθ z+r • fderiv ℝ Lθ z := by
      have h := fderiv_add (hRθ.differentiable (by simp) z)
        ((hLθ.const_smul r).differentiable (by simp) z)
      change fderiv ℝ (Rθ+r • Lθ) z = _ at h
      rw [hExpr,h]
      have hh := fderiv_const_smul (hLθ.differentiable (by simp) z) r
      change fderiv ℝ (r • Lθ) z = _ at hh
      exact congrArg (fderiv ℝ Rθ z + ·) hh
    have hNum : Qθ*r^2+r*(2*Pθ) ≤ (Qθ+2*Pθ)*r := by
      have hh := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ Qθ*r by positivity)
      nlinarith only [hh]
    constructor
    · rw [hExpr',Pi.add_apply,Pi.smul_apply]
      exact ((norm_add_le _ _).trans (add_le_add hRem.1 (by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hLin.1 hr.le))).trans hNum
    · rw [hDExpr]
      exact ((norm_add_le _ _).trans (add_le_add hRem.2 (by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hLin.2 hr.le))).trans hNum
  have hRNorm (v : SmoothData dim) : ‖smoothBallSobolev 0 (smoothDivergenceData Rθ hRθ v)‖ ≤
      S*Qθ*r^2*‖smoothBallSobolev 2 v‖ :=
    (norm_smoothBallSobolev_negativeDivergence_le hRθ v _ (by positivity) hLocR).trans_eq (by ring)
  have hANorm (v : SmoothData dim) : ‖smoothBallSobolev 0 (smoothDivergenceData Aθ hAθ v)‖ ≤
      G*r*‖smoothBallSobolev 2 v‖ :=
    (norm_smoothBallSobolev_negativeDivergence_le hAθ v _ (by positivity) hLocA).trans_eq (by dsimp only [G]; ring)
  let U := smoothBallSobolev 2 u
  have hQNorm : ‖smoothBallSobolev 2 qθ‖ ≤ C*(S*(2*Pθ))*‖U‖ := by
    let g := smoothScale (-1) (smoothDivergenceData Lθ hLθ u)
    have hh (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
        negativeBallDivergence A0 qθ.1 z = g.1 z := by
      rw [negativeBallDivergence_congr_germ (hA0Germ z hz) EventuallyEq.rfl]
      simpa only [g,smoothScale,smoothDivergenceData,Pi.smul_apply,smul_eq_mul,neg_one_mul] using
        negativeBallDivergence_flat_harmonicFiniteDriftVariation ellθ f z
    refine (norm_smooth_zeroDirichlet_le_of_forcing F0 hF0Ell qθ g
      (harmonicFiniteDriftVariationSmooth_trace ellθ f) hh).trans ?_
    rw [smoothBallSobolev_scale,norm_smul,Real.norm_eq_abs,abs_neg,abs_one,one_mul]
    exact (mul_le_mul hInv0
      (norm_smoothBallSobolev_negativeDivergence_le hLθ u _ (by positivity) hLocL) (norm_nonneg _) hC).trans_eq (by ring)
  obtain ⟨b₀,hb₀,hbT,hbH,_⟩ := exists_native_classicalBallPoisson 0 F hEll u
  obtain ⟨v₀,hv₀,hvT,hvH,_⟩ := exists_native_classicalBallPoisson 0 F hEll (harmonicFiniteSmooth fθ)
  rw [harmonicFiniteSmooth_rotation] at hvT
  let b : SmoothData dim := ⟨b₀,hb₀⟩
  let bθ : SmoothData dim := ⟨v₀,hv₀⟩
  let du := smoothDifference b u
  have hDu : ‖smoothBallSobolev 2 du‖ ≤ C*D*r*‖U‖ := by
    let g := smoothScale (-1) (smoothDivergenceData AF hAF u)
    have hT : EqOn du.1 0 (standardSphere dim) := fun z hz => sub_eq_zero.mpr (hbT hz)
    have hh (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
        negativeBallDivergence A du.1 z = g.1 z := by
      change negativeBallDivergence A (b.1-u.1) z = _
      simp only [g,smoothScale,smoothDivergenceData,Pi.smul_apply,smul_eq_mul,neg_one_mul]
      rw [negativeBallDivergence_sub_solution ha b u,hbH hz,Pi.zero_apply,zero_sub,hAFEq,
        negativeBallDivergence_sub_coefficient ha hA0 u,
        negativeBallDivergence_congr_germ (hA0Germ z hz) EventuallyEq.rfl,
        negativeBallDivergence_flat_harmonicFiniteSmooth f z,sub_zero]
    refine (norm_smooth_zeroDirichlet_le_of_forcing F hEll du g hT hh).trans ?_
    rw [smoothBallSobolev_scale,norm_smul,Real.norm_eq_abs,abs_neg,abs_one,one_mul]
    exact (mul_le_mul hInvA (hAFNorm u) (norm_nonneg _) hC).trans_eq (by ring)
  let w := angularBallCorrection i j b bθ
  let e := smoothDifference w (smoothScale r qθ)
  have hEq (z : X dim) : e.1 z = w.1 z-r*qθ.1 z := rfl
  refine ⟨b,bθ,e,hbT,hvT,?_,?_,hEq,?_⟩
  · intro z hz
    rw [← negativeBallDivergence_congr_germ (hAgerm z hz) EventuallyEq.rfl]
    exact hbH hz
  · intro z hz
    rw [← negativeBallDivergence_congr_germ (hAgerm z hz) EventuallyEq.rfl]
    exact hvH hz
  let g₁ := smoothDivergenceData Aθ hAθ du
  let g₂ := smoothDivergenceData Rθ hRθ u
  let g₃ := smoothDivergenceData AF hAF qθ
  let g := smoothDifference (smoothDifference (smoothScale (-1) g₁) g₂) (smoothScale r g₃)
  have heT : EqOn e.1 0 (standardSphere dim) := by
    intro z hz
    rw [hEq,show w.1 z = 0 from angularBallCorrection_trace_zero i j b bθ u hbT hvT hz,
      show qθ.1 z = 0 from harmonicFiniteDriftVariationSmooth_trace ellθ f hz,mul_zero,sub_zero]
    rfl
  have heEq (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      negativeBallDivergence A e.1 z = g.1 z := by
    change negativeBallDivergence A (w.1-r • qθ.1) z = _
    simp only [g,g₁,g₂,g₃,smoothDifference,smoothScale,smoothDivergenceData,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul,neg_one_mul]
    have hStep := negativeBallDivergence_sub_solution ha w (smoothScale r qθ) z
    change negativeBallDivergence A (w.1-r • qθ.1) z =
      negativeBallDivergence A w.1 z-negativeBallDivergence A (r • qθ.1) z at hStep
    rw [hStep,negativeBallDivergence_angularBallCorrection i j ha b bθ hbH hvH hz]
    change -negativeBallDivergence Aθ b.1 z-negativeBallDivergence A (r • qθ.1) z = _
    rw [negativeBallDivergence_const_smul_solution ha qθ]
    simp only [du,smoothDifference,Rθ,hAFEq]
    have hRes := negativeBallDivergence_sub_coefficient hAθ (hLθ.const_smul r) u z
    change negativeBallDivergence (Aθ-r • Lθ) u.1 z =
      negativeBallDivergence Aθ u.1 z-negativeBallDivergence (r • Lθ) u.1 z at hRes
    rw [negativeBallDivergence_sub_solution hAθ b u,hRes,
      negativeBallDivergence_const_smul_coefficient Lθ u.1 r z,
      negativeBallDivergence_sub_coefficient ha hA0 qθ,
      negativeBallDivergence_congr_germ (hA0Germ z hz) EventuallyEq.rfl,
      negativeBallDivergence_flat_harmonicFiniteDriftVariation ellθ f z]
    ring
  refine (norm_smooth_zeroDirichlet_le_of_forcing F hEll e g heT heEq).trans ?_
  have hg : ‖smoothBallSobolev 0 g‖ ≤ G*r*(C*D*r*‖U‖)+S*Qθ*r^2*‖U‖+
      r*(D*r*(C*(S*(2*Pθ))*‖U‖)) := by
    simp only [g,smoothBallSobolev_difference,smoothBallSobolev_scale]
    refine ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_one,one_mul,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    refine add_le_add (add_le_add ((hANorm du).trans ?_) (hRNorm u))
      (mul_le_mul_of_nonneg_left ((hAFNorm qθ).trans ?_) hr.le)
    · exact mul_le_mul_of_nonneg_left hDu (by positivity)
    · exact mul_le_mul_of_nonneg_left hQNorm (by positivity)
  exact (mul_le_mul hInvA hg (norm_nonneg _) hC).trans_eq (by dsimp only [B]; ring)

end CalderonN
