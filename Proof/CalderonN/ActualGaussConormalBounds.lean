module

public import Proof.CalderonN.ActualGaussConormalCore
public import Proof.CalderonN.SmoothTraceAngularOrder
public import Proof.CalderonN.FiniteDoubleConormalTrace

import Proof.CalderonN.ActualHigherConormalDegree
import Proof.CalderonN.ActualSmoothConormalMultiplier
import Mathlib.Tactic

/-! The fixed-center conormal and its degree and rotation commutators
have order one on the angular levels of the physical error form. The
estimates hold for every choice of the genuine Gauss data. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothTraceAngularBound_one_of_mid_and_high (hn : 3 ≤ dim)
    (T S : Module.End ℝ (SmoothSphereTrace dim)) (C : ℝ) (hC : 0 ≤ C)
    (hAdj : SmoothTraceAdjoint hn S T)
    (hM : ∀ u,traceOrderNorm hn 1 (T u) ≤ C*traceOrderNorm hn 2 u)
    (hH : ∀ u,traceOrderNorm hn 2 (T u) ≤ C*traceOrderNorm hn 3 u)
    (hAH : ∀ u,traceOrderNorm hn 2 (S u) ≤ C*traceOrderNorm hn 3 u) :
    SmoothTraceAngularBound hn 1 C T := by
  intro i j hij u
  have hL : traceOrderNorm hn 0 (T u) ≤ C*traceOrderNorm hn 1 u := by
    have h₁ : traceOrderExponent (2 : Fin 4) = (1/2:ℝ) := by norm_num [traceOrderExponent,Fin.reduceFinMk]
    have h₂ : traceOrderExponent (3 : Fin 4) = (3/2:ℝ) := by norm_num [traceOrderExponent,Fin.reduceFinMk]
    have h₃ : traceOrderExponent (0 : Fin 4) = -(3/2:ℝ) := by norm_num [traceOrderExponent,Fin.reduceFinMk]
    have h₄ : traceOrderExponent (1 : Fin 4) = -(1/2:ℝ) := by norm_num [traceOrderExponent,Fin.reduceFinMk]
    have hAH' (u : SmoothSphereTrace dim) :
        ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (S u)‖ ≤
          C*‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖ := by
      have h := hAH u
      unfold traceOrderNorm at h
      rw [smoothSphereTraceSobolev_order_eq hn h₁ _ (by norm_num),
        smoothSphereTraceSobolev_order_eq hn h₂ _ (by norm_num)] at h
      exact h
    have h := norm_smoothTrace_adjoint_of_bound hn (3/2:ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) S T hAdj C hC hAH' u
    unfold traceOrderNorm
    rw [smoothSphereTraceSobolev_order_eq hn h₃ _ (by norm_num),
      smoothSphereTraceSobolev_order_eq hn h₄ _ (by norm_num)]
    exact h
  have hSmall := j.isLt
  have hCases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hCases with h | h | h
  · rw [show i = 0 from Fin.ext h,show j = 1 from Fin.ext (by omega)]
    exact hL
  · rw [show i = 1 from Fin.ext h,show j = 2 from Fin.ext (by omega)]
    exact hM u
  · rw [show i = 2 from Fin.ext h,show j = 3 from Fin.ext (by omega)]
    exact hH u

theorem traceOrderNorm_half_eq (hn : 3 ≤ dim) (u : SmoothSphereTrace dim) :
    traceOrderNorm hn 2 u = ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ := by
  unfold traceOrderNorm
  rw [smoothSphereTraceSobolev_order_eq hn (show traceOrderExponent (2:Fin 4) = 1/2 by
    norm_num [traceOrderExponent,Fin.reduceFinMk]) _ (by norm_num)]

theorem traceOrderNorm_negHalf_eq (hn : 3 ≤ dim) (u : SmoothSphereTrace dim) :
    traceOrderNorm hn 1 u = ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) u‖ := by
  unfold traceOrderNorm
  rw [smoothSphereTraceSobolev_order_eq hn (show traceOrderExponent (1:Fin 4) = -(1/2) by
    norm_num [traceOrderExponent,Fin.reduceFinMk]) _ (by norm_num)]

theorem traceOrderNorm_threeHalf_eq (hn : 3 ≤ dim) (u : SmoothSphereTrace dim) :
    traceOrderNorm hn 3 u = ‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖ := by
  unfold traceOrderNorm
  rw [smoothSphereTraceSobolev_order_eq hn (show traceOrderExponent (3:Fin 4) = 3/2 by
    norm_num [traceOrderExponent,Fin.reduceFinMk]) _ (by norm_num)]

theorem uniform_actualGauss_conormal_angularBounds (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ x ∈ Y, ∀ F : ActualGaussFiberData d x,
      let R := ((d.radius x)^2)⁻¹ • F.conormalRemainder
      let B := F.flatDegree
      SmoothTraceAdjoint hn R R ∧ SmoothTraceAngularBound hn 1 C R ∧
        (∀ i j,SmoothTraceAngularBound hn 1 C (smoothTraceAngularComm i j R)) ∧
        SmoothTraceAngularBound hn 1 C (B*R-R*B) := by
  obtain ⟨η,CL,CH,C₀,C₁,C₂,C₃,hη,hCL,hCH,hC₀,hC₁,hC₂,hC₃,h₀⟩ :=
    uniform_actual_higher_conormal_degree_comm (Y:=Y) hn hY hΩ hm K ρ c₀ M Cj hK hρ
  let C := CL+CH+C₀+C₁+C₂+C₃
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε hε hSmall d hd x hx F
  let r := d.radius x
  have hr : 0 < r := (hd.2.2.2.2.1.2 x hx).1
  let R := (r^2)⁻¹ • F.conormalRemainder
  let B := F.flatDegree
  obtain ⟨A,hA,lo,hi,hEll,S,T,hAeq,hAdj,hT,hR,hRot,hD⟩ := h₀ floor hf ε hε hSmall d hd x hx
  have hRT : F.conormalRemainder = T := F.conormalRemainder_eq_of_actual hA S
    (hAeq.mono (ball_subset_ball (by norm_num))) T hT
  have hB : B = smoothTraceFlatDegree hA hEll S := smoothTraceFlatDegree_eq hn
    F.smoothCoefficient hA F.ellipticCoefficient hEll F.solve S
  have hGen (Q U : Module.End ℝ (SmoothSphereTrace dim))
      (hQ : Q = (r^2)⁻¹ • U) (A B : ℝ) (hAC : A ≤ C) (hBC : B ≤ C)
      (hU : ∀ u,traceOrderNorm hn 1 (U u) ≤ A*r^2*traceOrderNorm hn 2 u ∧
        traceOrderNorm hn 2 (U u) ≤ B*r^2*traceOrderNorm hn 3 u) (u : SmoothSphereTrace dim) :
      traceOrderNorm hn 1 (Q u) ≤ C*traceOrderNorm hn 2 u ∧
        traceOrderNorm hn 2 (Q u) ≤ C*traceOrderNorm hn 3 u := by
    have hr₂ := pow_pos hr 2
    rw [hQ,LinearMap.smul_apply]
    have hNorm (i : Fin 4) : traceOrderNorm hn i ((r^2)⁻¹ • U u) =
        (r^2)⁻¹*traceOrderNorm hn i (U u) := by
      simp only [traceOrderNorm,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr₂)]
    constructor
    · rw [hNorm]
      exact (mul_le_mul_of_nonneg_left (hU u).1 (inv_nonneg.mpr hr₂.le)).trans
        ((by
          rw [show (r^2)⁻¹*(A*r^2*traceOrderNorm hn 2 u) = A*traceOrderNorm hn 2 u by field_simp]
          exact mul_le_mul_of_nonneg_right hAC (norm_nonneg _)) : _ ≤ _)
    · rw [hNorm]
      exact (mul_le_mul_of_nonneg_left (hU u).2 (inv_nonneg.mpr hr₂.le)).trans
        ((by
          rw [show (r^2)⁻¹*(B*r^2*traceOrderNorm hn 3 u) = B*traceOrderNorm hn 3 u by field_simp]
          exact mul_le_mul_of_nonneg_right hBC (norm_nonneg _)) : _ ≤ _)
  have hRS : SmoothTraceAdjoint hn R R := by
    dsimp only [R]
    rw [hRT]
    exact hAdj.const_smul (r^2)⁻¹
  have hRE (u : SmoothSphereTrace dim) := hGen R T (by simp only [R,hRT]) C₀ C₁
    (by dsimp only [C]; linarith) (by dsimp only [C]; linarith)
    (fun u => by simpa only [traceOrderNorm_negHalf_eq,traceOrderNorm_half_eq,traceOrderNorm_threeHalf_eq] using hR u) u
  refine ⟨hRS,smoothTraceAngularBound_one_of_mid_and_high hn R R C hC hRS
    (fun u => (hRE u).1) (fun u => (hRE u).2) (fun u => (hRE u).2),?_,?_⟩
  · intro i j
    let W := smoothTraceAngularComm i j R
    have hW : W = (r^2)⁻¹ • smoothTraceAngularComm i j T := by
      simp only [W,R,hRT,smoothTraceAngularComm,mul_smul_comm,smul_mul_assoc]
      ext u : 1
      simp only [LinearMap.sub_apply,LinearMap.smul_apply,smul_sub]
    have hWS : SmoothTraceAdjoint hn W W := SmoothTraceAdjoint.rotation_commutator_symmetric hn i j R hRS
    have hE (u : SmoothSphereTrace dim) := hGen W _ hW C₂ C₃
      (by dsimp only [C]; linarith) (by dsimp only [C]; linarith)
      (fun u => by
        simpa only [traceOrderNorm_negHalf_eq,traceOrderNorm_half_eq,traceOrderNorm_threeHalf_eq]
          using (hRot i j u)) u
    exact smoothTraceAngularBound_one_of_mid_and_high hn W W C hC hWS
      (fun u => (hE u).1) (fun u => (hE u).2) (fun u => (hE u).2)
  · let W := B*R-R*B
    let G := smoothTraceFlatDegree hA hEll S
    have hW : W = (r^2)⁻¹ • (G*T-T*G) := by
      simp only [W,R,hRT,hB,G,mul_smul_comm,smul_mul_assoc]
      ext u : 1
      simp only [LinearMap.sub_apply,LinearMap.smul_apply,smul_sub]
    have hBS : SmoothTraceAdjoint hn B B := smoothTraceFlatDegree_symmetric hn
      F.smoothCoefficient F.ellipticCoefficient F.solve
    have hWS : SmoothTraceAdjoint hn (-W) W := by
      have h := ((hBS.mul hRS).sub (hRS.mul hBS)).symm
      simpa only [W,neg_sub] using h
    have hE (u : SmoothSphereTrace dim) := hGen W _ hW CL CH
      (by dsimp only [C]; linarith) (by dsimp only [C]; linarith)
      (fun u => by
        simpa only [traceOrderNorm_negHalf_eq,traceOrderNorm_half_eq,traceOrderNorm_threeHalf_eq,G]
          using hD u) u
    exact smoothTraceAngularBound_one_of_mid_and_high hn W (-W) C hC hWS
      (fun u => (hE u).1) (fun u => (hE u).2) (fun u => by
        simpa only [traceOrderNorm,LinearMap.neg_apply,map_neg,norm_neg] using (hE u).2)

end CalderonN
