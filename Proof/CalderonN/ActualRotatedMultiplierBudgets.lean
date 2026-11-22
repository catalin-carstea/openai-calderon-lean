module

public import Proof.CalderonN.RotatedMultiplierBulkBounds
public import Proof.CalderonN.NormalizedAngularFluxBudgets
public import Proof.CalderonN.ActualAngularRadialWeights

import Proof.CalderonN.MatrixFieldJetNorms
import Proof.CalderonN.ActualRelativeWeakEnergyGerm
import Mathlib.Tactic

/-! Supply both Dirichlet estimates and the Gauss-weight estimates for the
same normalized coefficient extension. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem SmoothCoefficientC1Bound.of_native
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (F : SmoothCoefficientMatrix dim 2)
    (Q : ℝ) (hQ : ‖F‖ ≤ Q)
    (hEq : EqOn (coefficientMatrixField 2 F) A (ball (0:X dim) 1)) :
    SmoothCoefficientC1Bound A Q := by
  intro z hz
  let h := coefficientEntry_bounds_of_eqOn_native F Q hQ hEq z hz
  have hQ₀ := (norm_nonneg F).trans hQ
  exact ⟨(Matrix.norm_le_iff hQ₀).mpr (fun i j => by simpa only [Real.norm_eq_abs] using (h i j).1),
    norm_fderiv_matrix_le_of_entries A z (hA.differentiable (by simp) z) Q hQ₀ (fun i j => (h i j).2)⟩

theorem SmoothCoefficientC1Bound.enlarge {A : X dim → Mat dim} {C G : ℝ}
    (hA : SmoothCoefficientC1Bound A C) (hCG : C ≤ G) : SmoothCoefficientC1Bound A G :=
  fun z hz => ⟨(hA z hz).1.trans hCG,(hA z hz).2.trans hCG⟩

theorem SmoothCoefficientC1Bound.add {A B : X dim → Mat dim} {C G : ℝ}
    (hA : SmoothCoefficientC1Bound A C) (hB : SmoothCoefficientC1Bound B G)
    (ha : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ B) : SmoothCoefficientC1Bound (A+B) (C+G) := by
  intro z hz
  have h := fderiv_add (ha.differentiable (by simp) z) (hb.differentiable (by simp) z)
  change fderiv ℝ (A+B) z = _ at h
  rw [h]
  exact ⟨(norm_add_le _ _).trans (add_le_add (hA z hz).1 (hB z hz).1),
    (norm_add_le _ _).trans (add_le_add (hA z hz).2 (hB z hz).2)⟩

theorem SmoothCoefficientC1Bound.scale {A : X dim → Mat dim} {G s : ℝ}
    (hA : SmoothCoefficientC1Bound A G) (ha : ContDiff ℝ ∞ A) (hs : 0 ≤ s) :
    SmoothCoefficientC1Bound (s • A) (s*G) := by
  intro z hz
  have h := fderiv_const_smul (ha.differentiable (by simp) z) s
  change fderiv ℝ (s • A) z = _ at h
  rw [h]
  change ‖s • A z‖ ≤ _ ∧ ‖s • fderiv ℝ A z‖ ≤ _
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  exact ⟨mul_le_mul_of_nonneg_left (hA z hz).1 hs,mul_le_mul_of_nonneg_left (hA z hz).2 hs⟩

theorem DirichletMultiplierForcingBudget.enlarge
    {A : X dim → Mat dim} {m : SmoothData dim} {J C C' : ℝ} (hJ : 0 ≤ J)
    (h : DirichletMultiplierForcingBudget A m J C) (hCC' : C ≤ C') :
    DirichletMultiplierForcingBudget A m J C' := by
  intro n l a b ha hb u w s q t p hs hq ht hp hA hB v hv hV
  refine (h a b ha hb u w s q t p hs hq ht hp hA hB v hv hV).trans (mul_le_mul_of_nonneg_right hCC' ?_)
  exact add_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hs i) (hq i)) (norm_nonneg _))
    (Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (mul_nonneg (ht i) (hp i)) hJ) (norm_nonneg _))

theorem uniform_actual_rotated_multiplier_budgets (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C G F : ℝ, 0 < η ∧ 0 ≤ C ∧ 1 ≤ G ∧ 0 ≤ F ∧
      ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      let A₀ : X dim → Mat dim := fun _ => 1
      ∃ (A : X dim → Mat dim) (hA : ContDiff ℝ ∞ A)
        (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) (W D : SmoothData dim),
        EqOn A a (ball (0:X dim) (5/4)) ∧ 0 < r ∧ r ≤ 1 ∧
        (∀ z ∈ ball (0:X dim) 1,(A z).IsSymm) ∧
        SmoothDirichletDivergenceBudget A₀ (fun v => ‖smoothSobolev v‖) C ∧
        SmoothDirichletDivergenceBudget A (fun v => ‖smoothSobolev v‖) C ∧
        (∀ (b : SmoothData dim) (J : ℝ),0 ≤ J → SmoothMultiplierJetBound b J →
          DirichletMultiplierForcingBudget A₀ b J C ∧ DirichletMultiplierForcingBudget A b J C) ∧
        SmoothCoefficientC1Bound A G ∧ SmoothCoefficientC1Bound (A-A₀) (G*r) ∧
        (∀ v : SmoothData dim, EqOn (smoothBallConormal A v.1)
          (fun z => W.1 z*fderiv ℝ v.1 z z) (standardSphere dim)) ∧
        (∀ z,W.1 z = 1+D.1 z) ∧
        (∀ z ∈ ball (0:X dim) 1, (|W.1 z| ≤ F ∧ ‖fderiv ℝ W.1 z‖ ≤ F) ∧
          (|D.1 z| ≤ F*r ∧ ‖fderiv ℝ D.1 z‖ ≤ F*r)) ∧
        ∀ i j : I dim,
          let B := ballRotationCoefficient i j A
          let ell' := ell.comp (ballRotationGeneratorL i j)
          let L : X dim → Mat dim := fun z => ell' z • 1
          SmoothCoefficientC1Bound B (G*r) ∧ SmoothCoefficientC1Bound (B-r • L) (G*r^2) ∧
          SmoothCoefficientC1Bound L G ∧ ∃ V E : SmoothData dim,
            EqOn V.1 (sphereRotationDerivative i j W.1) (standardSphere dim) ∧
            (∀ z,V.1 z = r*ell' z+E.1 z) ∧
            (∀ z ∈ ball (0:X dim) 1, (|V.1 z| ≤ F*r ∧ ‖fderiv ℝ V.1 z‖ ≤ F*r) ∧
              (|E.1 z| ≤ F*r^2 ∧ ‖fderiv ℝ E.1 z‖ ≤ F*r^2)) := by
  obtain ⟨F₀,η_B,P,Q,Inv,hF₀,hη_B,hP,hQ,hInv,hInv₀,hBall⟩ :=
    uniform_normalized_ballTaylor_budgets (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η_A,P_A,Q_A,hη_A,hP_A,hQ_A,hAng⟩ :=
    uniform_actual_angular_coefficient_jets (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η_W,F_W,hη_W,hF_W,hWeight⟩ :=
    uniform_actual_angular_radial_weights (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  let a := max (fullC1OperatorBudget (dim:=dim)) (4*(dim:ℝ)^2)
  let c := (1/10:ℝ)
  let C := max (Inv*a) ((dim:ℝ)^2/c)
  let G := 1+P+Q+4*P_A+Q_A
  let F := 1+F_W
  let A₀ : X dim → Mat dim := fun _ => 1
  have hc : 0 < c := by norm_num [c]
  have hG : 1 ≤ G := by dsimp [G]; linarith only [hP,hQ,hP_A,hQ_A]
  have hC : 0 ≤ C := le_trans (by positivity : 0 ≤ (dim:ℝ)^2/c) (le_max_right _ _)
  have hCompat : Inv*fullC1OperatorBudget (dim:=dim) ≤ C ∧ (dim:ℝ)^2/c ≤ C :=
    ⟨(mul_le_mul_of_nonneg_left (le_max_left _ _) hInv).trans (le_max_left _ _),le_max_right _ _⟩
  have hF₀unit : EqOn (coefficientMatrixField 2 F₀) A₀ (ball (0:X dim) 1) :=
    fun z hz => hF₀ z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (ball_subset_closedBall hz))
  have hFlat := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
  have hEll₀ : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F₀) 1 1 :=
    ⟨hFlat.1,hFlat.2.1,fun z hz => hF₀unit hz ▸ hFlat.2.2 hz⟩
  have hCoer₀ (v : FixedBallH1Zero dim) :
      c*‖v‖^2 ≤ fixedBallSmoothEnergyL (contDiff_coefficientMatrixField 2 F₀).continuous
        (v : FixedBallH1 dim) (v : FixedBallH1 dim) := by
    have hEq := fixedBallSmoothEnergyL_eq_weak_of_eqOn
      (contDiff_coefficientMatrixField 2 F₀).continuous hF₀unit (v : FixedBallH1 dim) (v : FixedBallH1 dim)
    have h := fixedBallSmoothEnergy_zero_coercive continuous_const hFlat v
    rw [hEq]
    rw [fixedBallSmoothEnergyL_apply] at h
    change (1/5:ℝ)*‖v‖*‖v‖ ≤ energyFormH1 A₀ 0 0 (v : FixedBallH1 dim) (v : FixedBallH1 dim) at h
    dsimp only [c]
    nlinarith only [h,sq_nonneg ‖v‖]
  have hWeak₀ := smoothDirichletDivergenceBudget_congr hF₀unit
    (smoothDirichletDivergenceBudget_native F₀ hEll₀ Inv c C hInv₀ hc hCoer₀ hCompat).2
  have hInverse₀ (v g : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim))
      (hg : EqOn (negativeBallDivergence A₀ v.1) g.1 (ball (0:X dim) 1)) :
      ‖smoothBallSobolev 2 v‖ ≤ Inv*‖smoothBallSobolev 0 g‖ := by
    have hEq : EqOn (negativeBallDivergence (coefficientMatrixField 2 F₀) v.1) g.1 (ball (0:X dim) 1) := by
      intro z hz
      have hGerm : coefficientMatrixField 2 F₀ =ᶠ[𝓝 z] A₀ := by
        filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hF₀unit hx
      exact (negativeBallDivergence_congr_germ hGerm EventuallyEq.rfl).trans (hg hz)
    exact (norm_smooth_zeroDirichlet_le_of_forcing F₀ hEll₀ v g hv hEq).trans
      (mul_le_mul_of_nonneg_right hInv₀ (norm_nonneg _))
  let η := min η_B (min η_A (min η_W 1))
  refine ⟨η,C,G,F,lt_min hη_B (lt_min hη_A (lt_min hη_W zero_lt_one)),hC,hG,by dsimp [F]; positivity,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε :=
    (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have htail := hs.trans (min_le_right _ _)
  have htail' := htail.trans (min_le_right _ _)
  have hr₁ := hrε.trans (htail'.trans (min_le_right _ _))
  obtain ⟨Fn,_,lo,hi,hFA,_,hEll,_,hNear,_,hInvA,_,_,_,hCoerA⟩ :=
    hBall floor hf ε he (hs.trans (min_le_left _ _)) d hd y hy
  let A := coefficientMatrixField 2 Fn
  let hA := contDiff_coefficientMatrixField 2 Fn
  let S (f : SmoothData dim) := Classical.choice
    (exists_conormalTaylorSolutions_of_extension Fn F₀ hF₀ (fun _ _ => rfl) hEll ell f)
  obtain ⟨_,W,D,_,hW,hWD,hDW,hRotW⟩ :=
    hWeight floor hf ε he (htail'.trans (min_le_left _ _)) d hd y hy A hA hFA
  obtain ⟨hPos,hRot⟩ := (hAng floor hf ε he (htail.trans (min_le_left _ _)) d hd y hy).2 A hA hFA
  have hDiffEq : EqOn (coefficientMatrixField 2 (Fn-F₀)) (A-A₀) (ball (0:X dim) 1) := by
    intro z hz
    rw [coefficientMatrixField_two_sub]
    change A z-coefficientMatrixField 2 F₀ z = A z-A₀ z
    rw [hF₀unit hz]
  have hAA₀ : ContDiff ℝ ∞ (A-A₀) := hA.sub contDiff_const
  have hCA₀ := SmoothCoefficientC1Bound.of_native hAA₀ (Fn-F₀) ((P+Q)*r) hNear hDiffEq
  have hCG : P+Q ≤ G := by dsimp [G]; linarith only [hP_A,hQ_A]
  have hA_G : SmoothCoefficientC1Bound A G := by
    have h := hCA₀.add (smoothCoefficientC1Bound_flat (dim:=dim) 1 le_rfl) hAA₀ contDiff_const
    rw [show A-A₀+A₀ = A by abel] at h
    exact h.enlarge (by dsimp [G]; nlinarith only
      [hP_A,hQ_A,mul_le_mul_of_nonneg_left hr₁ (add_nonneg hP hQ)])
  refine ⟨A,hA,S,W,D,hFA,hr,hr₁,fun z hz => (hPos z (ball_subset_closedBall hz)).isHermitian.isSymm,
    hWeak₀,(smoothDirichletDivergenceBudget_native Fn hEll Inv c C hInvA hc hCoerA hCompat).2,
    ?_,hA_G,hCA₀.enlarge (mul_le_mul_of_nonneg_right hCG hr.le),hW,hWD,?_,?_⟩
  · intro b J hJ hm'
    constructor
    · exact DirichletMultiplierForcingBudget.enlarge hJ
        (dirichletMultiplierForcingBudget_of_inverse b J Inv hJ hInv hm' hInverse₀) (le_max_left _ _)
    · have hIA (v g : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim))
          (hg : EqOn (negativeBallDivergence A v.1) g.1 (ball (0:X dim) 1)) :
          ‖smoothBallSobolev 2 v‖ ≤ Inv*‖smoothBallSobolev 0 g‖ :=
        (norm_smooth_zeroDirichlet_le_of_forcing Fn hEll v g hv hg).trans
          (mul_le_mul_of_nonneg_right hInvA (norm_nonneg _))
      have hI : DirichletMultiplierForcingBudget A b J (Inv*a) :=
        dirichletMultiplierForcingBudget_of_inverse b J Inv hJ hInv hm' hIA
      have hI' : DirichletMultiplierForcingBudget A b J C :=
        DirichletMultiplierForcingBudget.enlarge hJ hI (le_max_left _ _)
      exact @hI'
  · intro z hz
    obtain ⟨_,_,_,hD₀,hD₁⟩ := hDW z (ball_subset_closedBall hz)
    have hD' : fderiv ℝ W.1 z = fderiv ℝ D.1 z := by
      rw [show W.1 = fun x => 1+D.1 x from funext hWD,
        fderiv_fun_add (differentiableAt_const (1:ℝ)) (D.2.differentiable (by simp) z)]
      simp
    have hD'' : F_W*r ≤ F_W := by
      simpa using mul_le_mul_of_nonneg_left hr₁ hF_W
    have hNum : F_W*r ≤ F*r := mul_le_mul_of_nonneg_right (by dsimp [F]; linarith) hr.le
    refine ⟨⟨?_,?_⟩,hD₀.trans hNum,hD₁.trans hNum⟩
    · rw [hWD z]
      exact (abs_add_le _ _).trans (by rw [abs_one]; exact add_le_add le_rfl (hD₀.trans hD''))
    · rw [hD']
      exact hD₁.trans (hD''.trans (by dsimp [F]; linarith))
  · intro i j
    let B := ballRotationCoefficient i j A
    let ell' := ell.comp (ballRotationGeneratorL i j)
    let L : X dim → Mat dim := fun z => ell' z • 1
    let R := B-r • L
    let hL : ContDiff ℝ ∞ L := ell'.contDiff.smul contDiff_const
    have hR : ContDiff ℝ ∞ R := (contDiff_ballRotationCoefficient i j hA).sub (hL.const_smul r)
    have hBound_R : SmoothCoefficientC1Bound R (Q_A*r^2) :=
      fun z hz => (hRot i j).2 z (ball_subset_closedBall hz)
    have hBound_L : SmoothCoefficientC1Bound L (4*P_A) := by
      intro z hz
      let L' := ell'.smulRight (1 : Mat dim)
      have hL' : ‖ell'‖ ≤ 4*P_A := by linarith only [(hRot i j).1,hP_A]
      constructor
      · change ‖ell' z • (1 : Mat dim)‖ ≤ _
        rw [norm_smul,norm_one,mul_one]
        exact ((ell'.le_opNorm z).trans (mul_le_of_le_one_right (norm_nonneg _) (mem_ball_zero_iff.mp hz).le)).trans hL'
      · change ‖fderiv ℝ (⇑L') z‖ ≤ _
        rw [ContinuousLinearMap.fderiv]
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        intro x
        rw [ContinuousLinearMap.smulRight_apply,norm_smul,norm_one,mul_one]
        exact (ell'.le_opNorm x).trans (mul_le_mul_of_nonneg_right hL' (norm_nonneg x))
    have hBound_B := hBound_R.add (hBound_L.scale hL hr.le) hR (hL.const_smul r)
    have hR_B : R+r • L = B := by dsimp only [R]; abel
    rw [hR_B] at hBound_B
    have hG' : 4*P_A+Q_A ≤ G := by dsimp [G]; linarith only [hP,hQ]
    have hLG : 4*P_A ≤ G := by linarith only [hG',hQ_A]
    have hQG : Q_A ≤ G := by linarith only [hG',hP_A]
    refine ⟨hBound_B.enlarge ?_,hBound_R.enlarge (mul_le_mul_of_nonneg_right hQG (sq_nonneg r)),
      hBound_L.enlarge hLG,?_⟩
    · have hNum := mul_le_mul_of_nonneg_left hr₁ (mul_nonneg hQ_A hr.le)
      calc
        Q_A*r^2+r*(4*P_A) ≤ (4*P_A+Q_A)*r := by nlinarith only [hNum]
        _ ≤ G*r := mul_le_mul_of_nonneg_right hG' hr.le
    · obtain ⟨_,V,E,hV,hE,hJets⟩ := hRotW i j
      refine ⟨V,E,hV,hE,fun z hz => ?_⟩
      obtain ⟨hV₀,hV₁,hE₀,hE₁⟩ := hJets z (ball_subset_closedBall hz)
      exact ⟨⟨hV₀.trans (by gcongr; dsimp [F]; linarith),hV₁.trans (by gcongr; dsimp [F]; linarith)⟩,
        hE₀.trans (by gcongr; dsimp [F]; linarith),hE₁.trans (by gcongr; dsimp [F]; linarith)⟩

end CalderonN
