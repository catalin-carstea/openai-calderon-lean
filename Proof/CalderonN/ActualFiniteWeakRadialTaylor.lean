module

public import Proof.CalderonN.FiniteRadialModelLowNorm
public import Proof.CalderonN.ActualRadialWeightJets
public import Proof.CalderonN.SmoothBallReciprocal

import Mathlib.Tactic

/-! The actual radial response at the weak Sobolev endpoint. Gauss' row
removes the conormal multiplier without an angular order loss. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The same radial Taylor difference as at the strong endpoint has a
uniform quadratic bound from finite (H^{1/2}) data to (H^{-1/2}). -/
theorem uniform_actual_finite_weak_radial_taylor (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ f : HarmonicFiniteCoefficients dim,
        let r := d.radius y
        let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
        let ell := firstDensityCenterLinear d y
        let u := harmonicFiniteSmooth f
        let q := harmonicFiniteDriftVariationSmooth ell f
        ∃ b E : SmoothData dim,
          EqOn b.1 u.1 (standardSphere dim) ∧
          EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
          (∀ z, E.1 z = fderiv ℝ b.1 z z-fderiv ℝ u.1 z z-r*fderiv ℝ q.1 z z) ∧
          ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) E‖ ≤
            B*r^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
  obtain ⟨η,A,hη,hA,hCon⟩ := uniform_actual_conormal_sobolev_taylor (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,C,hηW,hC,hWeight⟩ := uniform_actual_radial_weight_remainder (Y := Y) (by omega : 2 ≤ dim)
    hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηN,hηN,hN⟩ := uniform_normal_control_on_disk (Y := Y) hΩ (by omega : 2 ≤ m)
    K ρ c₀ M Cj hK hρ 1 zero_le_one
  let T := 2*Real.sqrt ((dim : ℝ)+3)
  let d0 := (dim : ℝ)^2
  let d1 := (1+T)*d0*C
  let Cinv := 2+8*C
  let B := T*Cinv*(A+T*C*d0+T*(2*C)*d1)
  let τ := min (min η ηW) (min ηN (1/(4*(C+1))))
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hd0 : 0 ≤ d0 := sq_nonneg _
  have hd1 : 0 ≤ d1 := by dsimp only [d1]; positivity
  have hI : 0 ≤ Cinv := by dsimp only [Cinv]; positivity
  refine ⟨τ,B,lt_min (lt_min hη hηW) (lt_min hηN (by positivity)),by dsimp only [B]; positivity,?_⟩
  intro floor hf ε hε hετ d hd y hy f
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth ell f
  let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
  obtain ⟨b,E,hbT,hbH,hEC,hEN⟩ := hCon floor hf ε hε
    (hετ.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy f
  obtain ⟨hℓ,R,hW,hR⟩ := hWeight floor hf ε hε
    (hετ.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have hrB : r*(4*(C+1)) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4*(C+1))).mp
    (hrε.trans (hετ.trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hr1 : r ≤ 1 := by nlinarith only [hrB,mul_nonneg hr.le hC]
  have hrC : 2*C*r ≤ 1/2 := by nlinarith only [hrB,hr]
  let D : SmoothData dim := ⟨fun z => r*ell z+R.1 z,(contDiff_const.mul ell.contDiff).add R.2⟩
  let W : SmoothData dim := ⟨fun z => 1+D.1 z,contDiff_const.add D.2⟩
  have hD (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) :
      |D.1 z| ≤ 2*C*r ∧ ‖fderiv ℝ D.1 z‖ ≤ 2*C*r := by
    have hR' := hR z hz
    have hBound : r*C+C*r^2 ≤ 2*C*r := by
      have h := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ C*r by positivity)
      nlinarith only [h]
    have hL : |ell z| ≤ C := (ell.le_opNorm z).trans (by
      simpa only [mul_one] using mul_le_mul hℓ (mem_closedBall_zero_iff.mp hz) (norm_nonneg z) hC)
    refine ⟨?_,?_⟩
    · change |r*ell z+R.1 z| ≤ _
      refine ((abs_add_le _ _).trans (add_le_add ?_ hR'.1)).trans hBound
      rw [abs_mul,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hL hr.le
    · have hE (x : X dim) : fderiv ℝ (fun w => r*ell w) x = r • ell := by
        change fderiv ℝ (r • ⇑ell) x = _
        rw [fderiv_const_smul (ell.differentiable x) r,ContinuousLinearMap.fderiv]
      change ‖fderiv ℝ (fun z => r*ell z+R.1 z) z‖ ≤ _
      have hDiff : DifferentiableAt ℝ (fun w => r*ell w) z :=
        (differentiableAt_const r).mul (ell.differentiable z)
      rw [fderiv_fun_add hDiff (R.2.differentiable (by simp) z),hE]
      refine ((norm_add_le _ _).trans (add_le_add ?_ hR'.2)).trans hBound
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hℓ hr.le
  have hWpos (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : (1/2 : ℝ) ≤ W.1 z := by
    change (1/2 : ℝ) ≤ 1+D.1 z
    linarith only [(abs_le.mp (hD z hz).1).1,hrC]
  have hWder (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : ‖fderiv ℝ W.1 z‖ ≤ 2*C*r := by
    change ‖fderiv ℝ (fun x => 1+D.1 x) z‖ ≤ _
    rw [fderiv_fun_add (differentiableAt_const (1 : ℝ)) (D.2.differentiable (by simp) z),
      fderiv_fun_const,Pi.zero_apply,zero_add]
    exact (hD z hz).2
  obtain ⟨WInv,hWI,hWIn⟩ := exists_smoothBall_reciprocal W (by positivity)
    hWpos hWder
  let U := smoothBallRadialDerivative u
  let Q := smoothBallRadialDerivative q
  let bR := smoothBallRadialDerivative b
  let RU := smoothDataMul R U
  let DQ := smoothDataMul D Q
  let e : smoothBallDataSubmodule dim := ⟨E.1,E.2⟩
  let p1 : smoothBallDataSubmodule dim := ⟨RU.1,RU.2⟩
  let p2 : smoothBallDataSubmodule dim := ⟨DQ.1,DQ.2⟩
  let z' := e-p1-r • p2
  let Z : SmoothData dim := ⟨z'.1,smoothBallData_contDiff z'⟩
  let eR : SmoothData dim := ⟨fun z => bR.1 z-U.1 z-r*Q.1 z,
    (bR.2.sub U.2).sub (contDiff_const.mul Q.2)⟩
  refine ⟨b,eR,hbT,hbH,fun _ => rfl,?_⟩
  have hEqR : EqOn eR.1 (smoothDataMul WInv Z).1 (standardSphere dim) := by
    intro z hz
    have hzB := sphere_subset_closedBall hz
    have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
    have hw := frameVector_mem_disk d.γ d.frame y z 1 hFrame hzB
    have hNear := (hN floor hf ε hε (hετ.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy _ hw).1.1
    have hRow := hd.inner_actualNormalFlux_radial_row (by omega : 2 ≤ dim) hΩ
      (zero_lt_one.trans_le hK) hy hr.ne' z hNear b.1
    have hV : W.1 z = firstNormalRadialWeight d y r z := by
      change 1+(r*ell z+R.1 z) = _
      rw [← add_assoc]
      exact hW hz
    have hE : E.1 z = W.1 z*bR.1 z-U.1 z-r*(ell z*U.1 z+Q.1 z) := by
      have hh := hEC hz
      change E.1 z = ⟪z,smoothBallFlux a b.1 z⟫_ℝ-U.1 z-r*(ell z*U.1 z+Q.1 z) at hh
      exact hh.trans (by rw [hRow,← hV]; rfl)
    have hZ : Z.1 z = E.1 z-R.1 z*U.1 z-r*(D.1 z*Q.1 z) := rfl
    change bR.1 z-U.1 z-r*Q.1 z = WInv.1 z*Z.1 z
    have hZE : Z.1 z = W.1 z*(bR.1 z-U.1 z-r*Q.1 z) := by
      rw [hZ,hE]
      have hWz : W.1 z = 1+r*ell z+R.1 z := by dsimp only [W,D]; ring
      have hDz : D.1 z = r*ell z+R.1 z := rfl
      rw [hDz,hWz]
      ring
    rw [hWI hzB,hZE]
    change _ = (W.1 z)⁻¹*(W.1 z*(bR.1 z-U.1 z-r*Q.1 z))
    have hne : W.1 z ≠ 0 := by linarith only [hWpos z hzB]
    rw [← mul_assoc,inv_mul_cancel₀ hne,one_mul]
  rw [smoothBoundarySobolev_eq_of_eqOn hn (-(1/2 : ℝ)) (by norm_num) eR
    (smoothDataMul WInv Z) hEqR]
  have hU : ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) U‖ ≤ d0*‖L f‖ :=
    norm_flat_finite_radial_low_le hn f
  have hQ : ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) Q‖ ≤ d1*‖L f‖ :=
    (norm_first_finite_radial_low_le hn ell f).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ (by positivity)) (norm_nonneg (L f)))
  have hP1 : ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) RU‖ ≤
      T*(C*r^2)*(d0*‖L f‖) := by
    have hG (z : X dim) (hz : z ∈ (fixedBallOpens dim : Set (X dim))) : ‖gradient R.1 z‖ ≤ C*r^2 := by
      rw [gradient,LinearIsometryEquiv.norm_map]
      exact (hR z (ball_subset_closedBall hz)).2
    refine (norm_smoothBoundarySobolev_mul_negHalf_le hn R U (C := C*r^2) (by positivity)
      (fun z hz => (hR z (ball_subset_closedBall hz)).1) hG).trans ?_
    exact mul_le_mul_of_nonneg_left hU (by positivity)
  have hP2 : ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) DQ‖ ≤
      T*(2*C*r)*(d1*‖L f‖) := by
    have hG (z : X dim) (hz : z ∈ (fixedBallOpens dim : Set (X dim))) : ‖gradient D.1 z‖ ≤ 2*C*r := by
      rw [gradient,LinearIsometryEquiv.norm_map]
      exact (hD z (ball_subset_closedBall hz)).2
    refine (norm_smoothBoundarySobolev_mul_negHalf_le hn D Q (C := 2*C*r) (by positivity)
      (fun z hz => (hD z (ball_subset_closedBall hz)).1) hG).trans ?_
    exact mul_le_mul_of_nonneg_left hQ (by positivity)
  let X' := smoothBoundarySobolevLinear hn (-(1/2 : ℝ)) (by norm_num)
  have hZ : ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) Z‖ ≤
      (A+T*C*d0+T*(2*C)*d1)*r^2*‖L f‖ := by
    change ‖X' (e-p1-r • p2)‖ ≤ _
    rw [map_sub,map_sub,map_smul]
    have hEN' : ‖X' e‖ ≤ A*r^2*‖L f‖ := hEN
    have hP1' : ‖X' p1‖ ≤ T*(C*r^2)*(d0*‖L f‖) := hP1
    have hP2' : ‖X' p2‖ ≤ T*(2*C*r)*(d1*‖L f‖) := hP2
    have hP2r : ‖r • X' p2‖ ≤ r*(T*(2*C*r)*(d1*‖L f‖)) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hP2' hr.le
    calc
      _ ≤ ‖X' e‖+‖X' p1‖+‖r • X' p2‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ A*r^2*‖L f‖+T*(C*r^2)*(d0*‖L f‖)+r*(T*(2*C*r)*(d1*‖L f‖)) :=
        add_le_add (add_le_add hEN' hP1') hP2r
      _ = _ := by ring
  have hInv0 (z : X dim) (hz : z ∈ (fixedBallOpens dim : Set (X dim))) : |WInv.1 z| ≤ Cinv :=
    (hWIn z (ball_subset_closedBall hz)).1.trans (by dsimp only [Cinv]; linarith)
  have hInv1 (z : X dim) (hz : z ∈ (fixedBallOpens dim : Set (X dim))) : ‖gradient WInv.1 z‖ ≤ Cinv := by
    rw [gradient,LinearIsometryEquiv.norm_map]
    refine (hWIn z (ball_subset_closedBall hz)).2.trans ?_
    dsimp only [Cinv]
    nlinarith only [mul_le_mul_of_nonneg_left hr1 hC]
  change ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) (smoothDataMul WInv Z)‖ ≤
    B*r^2*‖L f‖
  refine (norm_smoothBoundarySobolev_mul_negHalf_le hn WInv Z hI hInv0 hInv1).trans ?_
  exact (mul_le_mul_of_nonneg_left hZ (by positivity)).trans_eq (by dsimp only [B,T]; ring)

end CalderonN
