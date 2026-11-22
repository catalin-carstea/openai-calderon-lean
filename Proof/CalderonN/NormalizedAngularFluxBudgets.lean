module

public import Proof.CalderonN.DoubleAngularCoefficientJets
public import Proof.CalderonN.DoubleAngularBulkEstimates
public import Proof.CalderonN.NormalizedBallTaylorBudgets

import Mathlib.Tactic

/-! Strong and weak divergence budgets and the first two angular
coefficient jets for one common admitted normal ball. -/

public section

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothDirichletDivergenceBudget_congr
    {A B : X dim → Mat dim} (hAB : EqOn A B (ball (0 : X dim) 1))
    {N : SmoothData dim → ℝ} {C : ℝ} (hA : SmoothDirichletDivergenceBudget A N C) :
    SmoothDirichletDivergenceBudget B N C := by
  intro n a ha u q hq hB v hv hV
  apply hA n a ha u q hq hB v hv
  intro z hz
  have hG : A =ᶠ[𝓝 z] B := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hAB hw
  exact (negativeBallDivergence_congr_germ hG EventuallyEq.rfl).trans (hV hz)

theorem smoothDirichletDivergenceBudget_native (F : SmoothCoefficientMatrix dim 2)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi)
    (Inv c C : ℝ)
    (hInv : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ Inv)
    (hc : 0 < c)
    (hCoer : ∀ u : FixedBallH1Zero dim,
      c*‖u‖^2 ≤ fixedBallSmoothEnergyL (contDiff_coefficientMatrixField 2 F).continuous
        (u : FixedBallH1 dim) (u : FixedBallH1 dim))
    (hC : Inv*fullC1OperatorBudget (dim:=dim) ≤ C ∧ (dim:ℝ)^2/c ≤ C) :
    SmoothDirichletDivergenceBudget (coefficientMatrixField 2 F) (fun v => ‖smoothBallSobolev 2 v‖) C ∧
      SmoothDirichletDivergenceBudget (coefficientMatrixField 2 F) (fun v => ‖smoothSobolev v‖) C := by
  constructor
  · intro n a ha u q hq hB v hv hV
    exact (norm_smoothBallSobolev_two_le_of_divergence_sum F hEll Inv hInv a ha u q hq hB v hv hV).trans
      (mul_le_mul_of_nonneg_right hC.1 (Finset.sum_nonneg fun i _ => mul_nonneg (hq i) (norm_nonneg _)))
  · intro n a ha u q hq hB v hv hV
    exact (norm_smoothSobolev_le_of_divergence_sum F hEll c hc hCoer a ha u q hq
      (fun i z hz => (hB i z hz).1) v hv hV).trans
      (mul_le_mul_of_nonneg_right hC.2 (Finset.sum_nonneg fun i _ => mul_nonneg (hq i) (norm_nonneg _)))

theorem uniform_normalized_angularFlux_budgets (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ (F₀ : SmoothCoefficientMatrix dim 2) (η C G : ℝ),
      0 < η ∧ 0 ≤ C ∧ 0 ≤ G ∧
      (∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F₀ z = 1) ∧
      SmoothDirichletDivergenceBudget (fun _ => (1 : Mat dim)) (fun v => ‖smoothBallSobolev 2 v‖) C ∧
      SmoothDirichletDivergenceBudget (fun _ => (1 : Mat dim)) (fun v => ‖smoothSobolev v‖) C ∧
      ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
        Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
        let r := d.radius y
        let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
        let ell := firstDensityCenterLinear d y
        ∃ (F : SmoothCoefficientMatrix dim 2) (lo hi : ℝ),
          let A := coefficientMatrixField 2 F
          0 < r ∧ r ≤ 1 ∧ EqOn A a (ball (0 : X dim) (5/4)) ∧
          UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi ∧
          (∀ z ∈ ball (0 : X dim) 1,(A z).IsSymm) ∧
          SmoothDirichletDivergenceBudget A (fun v => ‖smoothBallSobolev 2 v‖) C ∧
          SmoothDirichletDivergenceBudget A (fun v => ‖smoothSobolev v‖) C ∧
          SmoothCoefficientC1Bound A G ∧ SmoothCoefficientC1Bound (A-(fun _ => 1)) (G*r) ∧
          ∀ i j k l : Fin dim,
            let J₁ := ballRotationGeneratorL i j
            let J₂ := ballRotationGeneratorL k l
            let A₁ := ballRotationCoefficient i j A
            let A₂ := ballRotationCoefficient k l A
            let A₁₂ := ballRotationCoefficient k l A₁
            let L (z : X dim) := ((ell.comp J₁).comp J₂) z • (1 : Mat dim)
            SmoothCoefficientC1Bound A₁ (G*r) ∧ SmoothCoefficientC1Bound A₂ (G*r) ∧
            SmoothCoefficientC1Bound A₁₂ (G*r) ∧ SmoothCoefficientC1Bound L G ∧
            SmoothCoefficientC1Bound (A₁₂-r • L) (G*r^2) := by
  obtain ⟨F₀,η_B,P_B,Q_B,Inv,hF₀,hη_B,_,_,hInv,hI₀,hBall⟩ :=
    uniform_normalized_ballTaylor_budgets (Y:=Y) hn hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨η_C,Q_C,hη_C,hQ_C,hC₂⟩ := uniform_normalized_coefficient_remainder_C2 (Y:=Y)
    hn hΩ (by omega) K ρ c₀ M Cj hK hρ 1 zero_le_one
  obtain ⟨η₁,P₁,Q₁,hη₁,hP₁,hQ₁,hFirst⟩ := uniform_actual_angular_coefficient_jets (Y:=Y)
    hn hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨η₂,P₂,Q₂,hη₂,hP₂,hQ₂,hSecond⟩ := uniform_actual_double_angular_coefficient_jets (Y:=Y)
    hn hY hΩ hm K ρ c₀ M Cj hK hρ
  let c := (1/10:ℝ)
  let C := max (Inv*fullC1OperatorBudget (dim:=dim)) ((dim:ℝ)^2/c)
  let G := 1+(P₁+Q_C)+(2*P₁+Q₁)+(4*P₂+Q₂)
  let A₀ : X dim → Mat dim := fun _ => 1
  let hFlat := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
  have hc : 0 < c := by dsimp [c]; norm_num
  have hCB : Inv*fullC1OperatorBudget (dim:=dim) ≤ C ∧ (dim:ℝ)^2/c ≤ C := ⟨le_max_left _ _,le_max_right _ _⟩
  have hF₀unit : EqOn (coefficientMatrixField 2 F₀) A₀ (ball (0 : X dim) 1) :=
    fun z hz => hF₀ z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (ball_subset_closedBall hz))
  have hEll₀ : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F₀) 1 1 := by
    refine ⟨hFlat.1,hFlat.2.1,fun z hz => ?_⟩
    rw [hF₀unit hz]
    exact hFlat.2.2 hz
  have hE₀ : fixedBallSmoothEnergyL (contDiff_coefficientMatrixField 2 F₀).continuous = fixedBallFlatEnergyL dim := by
    ext u v
    rw [fixedBallSmoothEnergyL_apply,fixedBallFlatEnergyL,fixedBallSmoothEnergyL_apply]
    unfold energyFormH1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with z hz
    rw [hF₀unit hz]
  have hCoer₀ (v : FixedBallH1Zero dim) :
      c*‖v‖^2 ≤ fixedBallSmoothEnergyL (contDiff_coefficientMatrixField 2 F₀).continuous
        (v : FixedBallH1 dim) (v : FixedBallH1 dim) := by
    rw [hE₀]
    have h := fixedBallSmoothEnergy_zero_coercive continuous_const hFlat v
    change (1/5:ℝ)*‖v‖*‖v‖ ≤ fixedBallFlatEnergyL dim (v : FixedBallH1 dim) (v : FixedBallH1 dim) at h
    dsimp only [c]
    nlinarith [sq_nonneg ‖v‖]
  obtain ⟨hI₀H,hI₀L⟩ := smoothDirichletDivergenceBudget_native F₀ hEll₀ Inv c C hI₀ hc hCoer₀ hCB
  let η := min (min η_B η_C) (min (min η₁ η₂) 1)
  refine ⟨F₀,η,C,G,lt_min (lt_min hη_B hη_C) (lt_min (lt_min hη₁ hη₂) zero_lt_one),
    hCB.2.trans' (by positivity),by dsimp [G]; positivity,hF₀,
    smoothDirichletDivergenceBudget_congr hF₀unit hI₀H,smoothDirichletDivergenceBudget_congr hF₀unit hI₀L,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  let htail := hs.trans (min_le_right (min η_B η_C) (min (min η₁ η₂) 1))
  let hhead := hs.trans (min_le_left (min η_B η_C) (min (min η₁ η₂) 1))
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε :=
    (le_mul_of_one_le_right hr.le (one_le_pow₀ (hf.trans (hd.2.2.2.2.1.2 y hy).2.1))).trans
      (hd.2.2.2.2.2 y hy).2
  have hr₁ : r ≤ 1 := hrε.trans (htail.trans (min_le_right _ _))
  obtain ⟨F,F₁,lo,hi,hFA,hFF₁,hEll,_,_,_,hIF,_,_,_,hCoer⟩ :=
    hBall floor hf ε he (hhead.trans (min_le_left _ _)) d hd y hy
  let A := coefficientMatrixField 2 F
  let hA := contDiff_coefficientMatrixField 2 F
  obtain ⟨hEll₁,hFirst'⟩ := hFirst floor hf ε he
    (htail.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  obtain ⟨hEll₂,hSecond'⟩ := hSecond floor hf ε he
    (htail.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy
  obtain ⟨hPos,hK₁⟩ := hFirst' A hA hFA
  have hSym (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : (A z).IsSymm :=
    (hPos z (ball_subset_closedBall hz)).isHermitian.isSymm
  obtain ⟨hIH,hIL⟩ := smoothDirichletDivergenceBudget_native F hEll Inv c C hIF hc hCoer hCB
  refine ⟨F,lo,hi,hr,hr₁,hFA,hEll,hSym,hIH,hIL,?_⟩
  have hLinear (ν : X dim →L[ℝ] ℝ) (q : ℝ) (hq : 0 ≤ q) (hν : ‖ν‖ ≤ q) :
      SmoothCoefficientC1Bound (fun z => ν z • (1 : Mat dim)) q := by
    intro z hz
    let L := ν.smulRight (1 : Mat dim)
    have hL : ‖L‖ ≤ q := by
      apply ContinuousLinearMap.opNorm_le_bound _ hq
      intro x
      rw [ContinuousLinearMap.smulRight_apply,norm_smul,norm_one,mul_one]
      exact (ν.le_opNorm x).trans (mul_le_mul_of_nonneg_right hν (norm_nonneg _))
    change ‖L z‖ ≤ q ∧ ‖fderiv ℝ (⇑L) z‖ ≤ q
    rw [ContinuousLinearMap.fderiv]
    exact ⟨(L.le_opNorm z).trans ((mul_le_mul hL (mem_ball_zero_iff.mp hz).le (norm_nonneg _) hq).trans_eq
      (mul_one _)),hL⟩
  have hRes (ν : X dim →L[ℝ] ℝ) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
      (hν : ‖ν‖ ≤ p) {B : X dim → Mat dim} (hB : ContDiff ℝ ∞ B)
      (hR : SmoothCoefficientC1Bound (B-r • (fun z => ν z • (1 : Mat dim))) (q*r^2)) :
      SmoothCoefficientC1Bound B ((p+q)*r) := by
    let L := fun z => ν z • (1 : Mat dim)
    let R := B-r • L
    have hL : ContDiff ℝ ∞ L := ν.contDiff.smul contDiff_const
    have hS : ContDiff ℝ ∞ (r • L) := hL.const_smul r
    have hB' : B = r • L+R := by dsimp only [R]; abel
    intro z hz
    obtain ⟨h₁,h₂⟩ := hLinear ν p hp hν z hz
    obtain ⟨h₃,h₄⟩ := hR z hz
    have hQ : r*p+q*r^2 ≤ (p+q)*r := by nlinarith [mul_le_mul_of_nonneg_left hr₁ (mul_nonneg hq hr.le)]
    have hD : fderiv ℝ (r • L) z = r • fderiv ℝ L z :=
      fderiv_const_smul (hL.differentiable (by simp) z) r
    have hRS : ContDiff ℝ ∞ R := hB.sub hS
    have hF := fderiv_add (hS.differentiable (by simp) z) (hRS.differentiable (by simp) z)
    change fderiv ℝ (r • L+R) z = fderiv ℝ (r • L) z+fderiv ℝ R z at hF
    rw [hB',hF,hD]
    change ‖r • L z+R z‖ ≤ _ ∧ ‖r • fderiv ℝ L z+fderiv ℝ R z‖ ≤ _
    exact ⟨((norm_add_le _ _).trans (add_le_add (by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left h₁ hr.le) h₃)).trans hQ,
      ((norm_add_le _ _).trans (add_le_add (by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left h₂ hr.le) h₄)).trans hQ⟩
  let D := A-A₀
  have hD₀ : SmoothCoefficientC1Bound D ((P₁+Q_C)*r) := by
    apply hRes ell P₁ Q_C hP₁ hQ_C hEll₁ (B:=D) (hA.sub contDiff_const)
    intro z hz
    have hS (w : X dim) (hw : w ∈ ball (0 : X dim) (5/4)) :
        (D-r • (fun x => ell x • (1 : Mat dim))) w = normalizedFirstCoefficientRemainder d y w := by
      change A w-1-r • (ell w • (1 : Mat dim)) = _
      have hVal : A w = _ := hFA hw
      rw [hVal,normalizedFirstCoefficientRemainder,add_smul,one_smul,← mul_smul]
      abel
    have hGerm : D-r • (fun x => ell x • (1 : Mat dim)) =ᶠ[𝓝 z] normalizedFirstCoefficientRemainder d y := by
      filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1:ℝ) ≤ 5/4) hz)]
        with w hw using hS w hw
    change ‖(D-r • (fun x => ell x • (1 : Mat dim))) z‖ ≤ _ ∧
      ‖fderiv ℝ (D-r • (fun x => ell x • (1 : Mat dim))) z‖ ≤ _
    rw [hGerm.eq_of_nhds,hGerm.fderiv_eq]
    have h := hC₂ floor hf ε he (hhead.trans (min_le_right _ _)) d hd y hy z (ball_subset_closedBall hz)
    exact ⟨h.2.1,h.2.2.1⟩
  have hD' : SmoothCoefficientC1Bound D (G*r) := fun z hz =>
    ⟨(hD₀ z hz).1.trans (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) hr.le),
      (hD₀ z hz).2.trans (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) hr.le)⟩
  have hA' : SmoothCoefficientC1Bound A G := by
    intro z hz
    have hDecomp : A = A₀+D := by dsimp only [D]; abel
    have hCa : ContDiff ℝ ∞ A₀ := contDiff_const
    have hDz : (P₁+Q_C)*r ≤ P₁+Q_C :=
      (mul_le_mul_of_nonneg_left hr₁ (by positivity : 0 ≤ P₁+Q_C)).trans_eq (mul_one _)
    have hDs : ContDiff ℝ ∞ D := hA.sub hCa
    have hF := fderiv_add (hCa.differentiable (by simp) z) (hDs.differentiable (by simp) z)
    change fderiv ℝ (A₀+D) z = fderiv ℝ A₀ z+fderiv ℝ D z at hF
    rw [hDecomp,hF]
    change ‖(1 : Mat dim)+D z‖ ≤ _ ∧ ‖fderiv ℝ (fun _ : X dim => (1 : Mat dim)) z+fderiv ℝ D z‖ ≤ _
    rw [fderiv_fun_const,Pi.zero_apply,zero_add]
    exact ⟨((norm_add_le _ _).trans (add_le_add (by rw [norm_one]) ((hD₀ z hz).1.trans hDz))).trans
      (by dsimp [G]; linarith),((hD₀ z hz).2.trans hDz).trans (by dsimp [G]; linarith)⟩
  refine ⟨hA',hD',fun i j k l => ?_⟩
  let B₁ := ballRotationCoefficient i j A
  let B₂ := ballRotationCoefficient k l A
  let B₁₂ := ballRotationCoefficient k l B₁
  let ell₂ := (ell.comp (ballRotationGeneratorL i j)).comp (ballRotationGeneratorL k l)
  let L := fun z => ell₂ z • (1 : Mat dim)
  obtain ⟨he₂,hR₂⟩ := hSecond' A hA hFA i j k l
  have hA12 : SmoothCoefficientC1Bound B₁₂ ((4*P₂+Q₂)*r) :=
    hRes ell₂ (4*P₂) Q₂ (by positivity) hQ₂ he₂
      (contDiff_ballRotationCoefficient k l (contDiff_ballRotationCoefficient i j hA))
      (fun z hz => hR₂ z (ball_subset_closedBall hz))
  have hAθ (p q : Fin dim) : SmoothCoefficientC1Bound (ballRotationCoefficient p q A) (G*r) := by
    obtain ⟨hE,hR⟩ := hK₁ p q
    have h := hRes (ell.comp (ballRotationGeneratorL p q)) (2*P₁) Q₁ (by positivity) hQ₁ hE
      (contDiff_ballRotationCoefficient p q hA) (fun z hz => hR z (ball_subset_closedBall hz))
    exact fun z hz =>
      ⟨(h z hz).1.trans (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) hr.le),
        (h z hz).2.trans (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) hr.le)⟩
  exact ⟨hAθ i j,hAθ k l,
    fun z hz => ⟨(hA12 z hz).1.trans (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) hr.le),
      (hA12 z hz).2.trans (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) hr.le)⟩,
    hLinear ell₂ G (by dsimp [G]; positivity) (he₂.trans (by dsimp [G]; linarith)),
    fun z hz => ⟨(hR₂ z (ball_subset_closedBall hz)).1.trans
        (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) (sq_nonneg r)),
      (hR₂ z (ball_subset_closedBall hz)).2.trans
        (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) (sq_nonneg r))⟩⟩

end CalderonN
