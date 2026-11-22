module

public import Proof.CalderonN.ActualGaussConormalCore
public import Proof.CalderonN.ActualSmoothConormalMultiplier

import Mathlib.Tactic

/-! The multiplier commutator bounds hold on the same scaled conormal
core used by the actual physical trace. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actualGauss_scaledConormal_multiplier_bounds (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ D : ActualGaussFiberData d y,
        ∀ (b : SmoothData dim) (J : ℝ), 0 ≤ J → SmoothMultiplierJetBound b J →
        ∀ u : SmoothSphereTrace dim,
          let T := ((d.radius y)^2)⁻¹ • D.conormalRemainder
          let B := smoothSphereTraceMul b
          let W := T*B-B*T
          ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (W u)‖ ≤
            C*J*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ ∧
          ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (W u)‖ ≤
            C*J*‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) u‖ := by
  obtain ⟨η,C,hη,hC,hEst⟩ := uniform_actual_smooth_conormal_multiplier (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε he hs d hd y hy D b J hJ hJets u
  dsimp only
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  obtain ⟨A,hA,S,hAa,hBound⟩ := hEst floor hf ε he hs d hd y hy
  let R (f : SmoothData dim) := (S f).remainder hA r
  let hAC := D.coefficientEq.trans
    ((hAa.mono (ball_subset_ball (by norm_num : (1:ℝ) ≤ 5/4))).symm)
  have hR (f : SmoothData dim) : D.conormalRemainder (smoothSphereTrace f) = smoothSphereTrace (R f) := by
    rw [D.conormalRemainder_apply]
    exact (smoothSphereTrace_eq_iff _ _).mpr (conormalTaylorSolutions_remainder_eqOn_of_coefficientEq
      D.smoothCoefficient hA D.ellipticCoefficient (D.solve f) (S f) hAC (fun _ _ => rfl) r)
  have hMul (f : SmoothData dim) :
      smoothSphereTraceMul b (smoothSphereTrace f) = smoothSphereTrace (smoothDataMul b f) := by
    apply Subtype.ext
    funext z
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
    rfl
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let f₀ : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  let W := smoothSubtractData (R (smoothDataMul b f₀)) (smoothDataMul b (R f₀))
  let P := D.conormalRemainder
  let B := smoothSphereTraceMul b
  let u := smoothSphereTrace f₀
  have hW : P (B u)-B (P u) = smoothSphereTrace W := by
    change P (B (smoothSphereTrace f₀))-B (P (smoothSphereTrace f₀)) = _
    rw [hMul,hR,hR,hMul]
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_sub,Pi.sub_apply,smoothSphereTrace_apply]
    rfl
  have hEq : (((r^2)⁻¹ • P)*B-B*((r^2)⁻¹ • P)) u = (r^2)⁻¹ • smoothSphereTrace W := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.smul_apply,map_smul,← smul_sub,hW]
  change ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (((((r^2)⁻¹ • P)*B-B*((r^2)⁻¹ • P))) u)‖ ≤
      C*J*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ ∧
    ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (((((r^2)⁻¹ • P)*B-B*((r^2)⁻¹ • P))) u)‖ ≤
      C*J*‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) u‖
  rw [hEq]
  have hb := hBound b J hJ hJets f₀
  simp only [u,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr)),
    smoothSphereTraceSobolev_apply]
  have hScale (X : ℝ) : (r^2)⁻¹*(C*J*r^2*X) = C*J*X := by
    field_simp [hr.ne']
  exact ⟨(mul_le_mul_of_nonneg_left hb.1 (by positivity)).trans_eq (hScale _),
    (mul_le_mul_of_nonneg_left hb.2 (by positivity)).trans_eq (hScale _)⟩

end CalderonN
