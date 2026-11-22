module

public import Proof.CalderonN.SharpRadialHalfBound
public import Proof.CalderonN.SmoothBoundaryMultiplier
public import Proof.CalderonN.DoubleAngularBulkEstimates

import Proof.CalderonN.SharpBallValueTrace
import Mathlib.Tactic

/-! The half-order conormal trace follows from the sharp value trace
applied to each coordinate derivative. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_smoothBoundarySobolev_half_le_H1 (hn : 3 ≤ dim) (u : SmoothData dim) :
    ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u‖ ≤
      Real.sqrt (((dim:ℝ)+3)/(unitSphereArea dim))*‖smoothSobolev u‖ := by
  have hArea : 0 < unitSphereArea dim := unitSphereArea_pos
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  apply sq_smoothBoundarySobolev_half_of_truncations hn
  intro k
  refine le_of_mul_le_mul_left ((sum_sharpBallValueTrace_le u k).trans_eq ?_) hArea
  rw [mul_pow,Real.sq_sqrt (by positivity),← mul_assoc,mul_div_cancel₀ _ hArea.ne']

@[expose] def smoothConormalData {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (u : SmoothData dim) : SmoothData dim :=
  ⟨smoothBallConormal A u.1,contDiff_smoothBallConormal hA u⟩

theorem norm_smoothConormalData_half_le (hn : 3 ≤ dim) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
      (q : ℝ), 0 ≤ q → SmoothCoefficientC1Bound A q → ∀ u : SmoothData dim,
        ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (smoothConormalData hA u)‖ ≤
          C*q*‖smoothBallSobolev 2 u‖ := by
  let H := Real.sqrt (((dim:ℝ)+3)/(unitSphereArea dim))
  let L := 2*Real.sqrt ((dim:ℝ)+3)
  let D := ∑ j : Fin dim,‖unitBallCoordinateDerivativeL fixedSobolevCalculus 1 j‖
  let C := (dim:ℝ)^2*(2*L*H*D)
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C,by dsimp only [C,L,H]; positivity,?_⟩
  intro A hA q hq hN u
  let S := smoothBoundarySobolevLinear hn (1/2 : ℝ) (by norm_num)
  let m (i j : Fin dim) : SmoothData dim :=
    ⟨fun z => z i*A z i j,(EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.mul ((matrixEntryL i j).contDiff.comp hA)⟩
  let w (j : Fin dim) := smoothDataCoordDeriv j u
  let V (i j : Fin dim) : smoothBallDataSubmodule dim :=
    ⟨(smoothDataMul (m i j) (w j)).1,(smoothDataMul (m i j) (w j)).2⟩
  let P := ∑ i : Fin dim,∑ j : Fin dim,V i j
  let v : SmoothData dim := ⟨P.1,smoothBallData_contDiff P⟩
  have hEq : (smoothConormalData hA u).1 = v.1 := by
    funext z
    change smoothBallConormal A u.1 z = P.1 z
    rw [smoothBallConormal,EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial,dotProduct,P,Submodule.coe_sum,Finset.sum_apply,smoothBallFlux_apply,V,
      smoothDataMul,m,w,smoothDataCoordDeriv,Pi.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hM (i j : Fin dim) (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      |(m i j).1 z| ≤ 2*q ∧ ‖fderiv ℝ (m i j).1 z‖ ≤ 2*q := by
    let E := matrixEntryL i j
    let Z := EuclideanSpace.proj (𝕜:=ℝ) i
    have hEz : |E (A z)| ≤ q := by
      exact (Matrix.norm_entry_le_entrywise_sup_norm (A z)).trans (hN z hz).1
    have hZz : |Z z| ≤ 1 := (PiLp.norm_apply_le z i).trans (mem_ball_zero_iff.mp hz).le
    have hEn : ‖E‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      rw [one_mul,matrixEntryL_apply]
      exact Matrix.norm_entry_le_entrywise_sup_norm x
    have hZn : ‖Z‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      rw [one_mul]
      exact PiLp.norm_apply_le x i
    have hDer : fderiv ℝ (E ∘ A) z = E.comp (fderiv ℝ A z) :=
      (E.hasFDerivAt.comp z (hA.differentiable (by simp) z).hasFDerivAt).fderiv
    have hDA : ‖fderiv ℝ (E ∘ A) z‖ ≤ q := by
      rw [hDer]
      exact (E.opNorm_comp_le _).trans
        ((mul_le_mul hEn (hN z hz).2 (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    change |Z z*(E (A z))| ≤ 2*q ∧ ‖fderiv ℝ (fun z => Z z*(E ∘ A) z) z‖ ≤ 2*q
    constructor
    · rw [abs_mul]
      nlinarith only [mul_le_mul hZz hEz (abs_nonneg _) zero_le_one,hq]
    · rw [fderiv_fun_mul Z.differentiableAt ((E.contDiff.comp hA).differentiable (by simp) z),
        ContinuousLinearMap.fderiv]
      refine (norm_add_le _ _).trans ?_
      simp only [norm_smul,Real.norm_eq_abs,Function.comp_apply]
      nlinarith only [mul_le_mul hZz hDA (norm_nonneg _) zero_le_one,
        mul_le_mul hEz hZn (norm_nonneg _) hq]
  have hW (j : Fin dim) : ‖smoothSobolev (w j)‖ ≤ D*‖smoothBallSobolev 2 u‖ := by
    let D_j := unitBallCoordinateDerivativeL fixedSobolevCalculus 1 j
    have hw : smoothSobolev (w j) = TauCeti.Wkp.firstOrder 0 (D_j (smoothBallSobolev 2 u)) := by
      rw [show D_j (smoothBallSobolev 2 u) = smoothBallSobolev 1 (w j) from
        unitBallCoordinateDerivativeL_smooth 1 j u,firstOrder_smoothBallSobolev]
    have hL : ‖D_j‖ ≤ D := Finset.single_le_sum (fun k _ => norm_nonneg (unitBallCoordinateDerivativeL fixedSobolevCalculus 1 k))
      (Finset.mem_univ j)
    rw [hw]
    exact (norm_unitBall_firstOrder_le 0 _).trans ((D_j.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _)))
  have hTerm (i j : Fin dim) : ‖S (V i j)‖ ≤ (2*L*H*D)*q*‖smoothBallSobolev 2 u‖ := by
    rw [smoothBoundarySobolevLinear_apply]
    have hMul := norm_smoothBoundarySobolev_mul_half_le hn (m i j) (w j) (C:=2*q) (by positivity)
      (fun z hz => (hM i j z hz).1) (fun z hz => by
        rw [gradient,LinearIsometryEquiv.norm_map]
        exact (hM i j z hz).2)
    have hw := (norm_smoothBoundarySobolev_half_le_H1 hn (w j)).trans
      (mul_le_mul_of_nonneg_left (hW j) (by positivity))
    exact (hMul.trans (mul_le_mul_of_nonneg_left hw (by positivity))).trans_eq (by ring)
  rw [smoothBoundarySobolev_eq_of_eqOn hn (1/2 : ℝ) (by norm_num) _ v (fun z _ => congrFun hEq z)]
  change ‖S P‖ ≤ _
  simp only [P,map_sum]
  calc
    _ ≤ ∑ i : Fin dim,∑ j : Fin dim,‖S (V i j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin dim,∑ _j : Fin dim,(2*L*H*D)*q*‖smoothBallSobolev 2 u‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hTerm i j
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,C]; ring

end CalderonN
