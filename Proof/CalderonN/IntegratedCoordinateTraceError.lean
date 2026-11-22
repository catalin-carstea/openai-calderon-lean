module

public import Proof.CalderonN.WeightedTraceErrorForm
public import Proof.CalderonN.ActualTraceSections

import Mathlib.Tactic

/-! Integrate the three allowed coordinate forms against the actual base
measure, using an integrable majorant of the two weighted trace energies. -/

public section

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTracePairing_eq_setIntegral (hn : 3 ≤ dim) (μ : X dim → ℝ)
    (u v : SmoothSupportedTraceSection Y) :
    smoothSupportedTracePairing hn μ u v =
      ∫ x in Y, μ x*⟪smoothSupportedTraceL2 hn u x,smoothSupportedTraceL2 hn v x⟫_ℝ := by
  unfold smoothSupportedTracePairing
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Y) (fun x hx => by
    rw [smoothSupportedTraceL2_eq_zero_off hn u hx,inner_zero_left,mul_zero])]

@[expose] def coordinateTraceEnergy (hn : 3 ≤ dim) (β : X dim → ℝ)
    (u : SmoothSupportedTraceSection Y) (x : X dim) : ℝ :=
  (β x)⁻¹*(∑ i : I dim,traceOrderNorm hn 2
    (smoothSupportedTraceFiberL x (smoothSupportedTraceBaseDiff (axis i) u))^2)+
      β x*traceOrderNorm hn 3 (smoothSupportedTraceFiberL x u)^2

theorem abs_coordinateTraceError_pairing_le (hn : 3 ≤ dim)
    (hY : IsOpen Y) (μ β e : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
    (hμ₀ : ∀ x ∈ Y,0 ≤ μ x) (hβ : ∀ x ∈ Y,0 < β x)
    (he : IntegrableOn e Y)
    (u : SmoothSupportedTraceSection Y)
    (hEnergy : ∀ x ∈ Y,μ x*coordinateTraceEnergy hn β u x ≤ e x)
    (G₂ : I dim → I dim → Module.End ℝ (SmoothSupportedTraceSection Y))
    (G₁ : I dim → Module.End ℝ (SmoothSupportedTraceSection Y))
    (G₀ : Module.End ℝ (SmoothSupportedTraceSection Y))
    (C : ℝ) (hC : 0 ≤ C)
    (hFiber : ∀ x ∈ Y,∃ (E₂ : I dim → I dim → Module.End ℝ (SmoothSphereTrace dim))
      (E₁ : I dim → Module.End ℝ (SmoothSphereTrace dim)) (E₀ : Module.End ℝ (SmoothSphereTrace dim)),
      (∀ i j,SmoothTraceAngularBound hn 1 (C*(β x)⁻¹) (E₂ i j)) ∧
      (∀ i,SmoothTraceAngularBound hn 2 C (E₁ i)) ∧
      SmoothTraceAngularBound hn 3 (C*β x) E₀ ∧
      (∀ i j w,smoothSupportedTraceFiberL x (G₂ i j w) = E₂ i j (smoothSupportedTraceFiberL x w)) ∧
      (∀ i w,smoothSupportedTraceFiberL x (G₁ i w) = E₁ i (smoothSupportedTraceFiberL x w)) ∧
      (∀ w,smoothSupportedTraceFiberL x (G₀ w) = E₀ (smoothSupportedTraceFiberL x w))) :
    let B := smoothSupportedTracePairingL hn hY μ hμ
    let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
    |(∑ i,∑ j,B (G₂ i j (D j u)) (D i u))+(∑ i,B (G₁ i (D i u)) u)+ B (G₀ u) u| ≤
      ((dim:ℝ)^2+dim+1)*C*(∫ x in Y,e x) := by
  dsimp only
  let B := smoothSupportedTracePairingL hn hY μ hμ
  let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let H (v w : SmoothSupportedTraceSection Y) (x : X dim) :=
    ⟪smoothSupportedTraceL2 hn v x,smoothSupportedTraceL2 hn w x⟫_ℝ
  let q₂ (i j : I dim) (x : X dim) := μ x*H (G₂ i j (D j u)) (D i u) x
  let q₁ (i : I dim) (x : X dim) := μ x*H (G₁ i (D i u)) u x
  let q₀ (x : X dim) := μ x*H (G₀ u) u x
  let q (x : X dim) := (∑ i,∑ j,q₂ i j x)+(∑ i,q₁ i x)+q₀ x
  let vol := (volume : Measure (X dim)).restrict Y
  have hInt (v w : SmoothSupportedTraceSection Y) : Integrable (fun x => μ x*H v w x) vol :=
    (integrable_smoothSupportedTracePairing_integrand_local hn hY μ hμ v w).integrableOn
  have h₂ (i : I dim) : Integrable (fun x => ∑ j,q₂ i j x) vol :=
    integrable_finsetSum Finset.univ (fun j _ => hInt (G₂ i j (D j u)) (D i u))
  have hS₂ : Integrable (fun x => ∑ i,∑ j,q₂ i j x) vol :=
    integrable_finsetSum Finset.univ (fun i _ => h₂ i)
  have hS₁ : Integrable (fun x => ∑ i,q₁ i x) vol :=
    integrable_finsetSum Finset.univ (fun i _ => hInt (G₁ i (D i u)) u)
  have hS₀ : Integrable q₀ vol := hInt (G₀ u) u
  have hq : Integrable q vol := (hS₂.add hS₁).add hS₀
  have hEq (v w : SmoothSupportedTraceSection Y) : B v w = ∫ x, μ x*H v w x ∂vol :=
    smoothSupportedTracePairing_eq_setIntegral hn μ v w
  have hSum₂ : (∑ i,∑ j,B (G₂ i j (D j u)) (D i u)) = ∫ x,∑ i,∑ j,q₂ i j x ∂vol := by
    rw [integral_finsetSum Finset.univ (fun i _ => h₂ i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hInt (G₂ i j (D j u)) (D i u))]
    exact Finset.sum_congr rfl (fun j _ => hEq _ _)
  have hSum₁ : (∑ i,B (G₁ i (D i u)) u) = ∫ x,∑ i,q₁ i x ∂vol := by
    rw [integral_finsetSum Finset.univ (fun i _ => hInt (G₁ i (D i u)) u)]
    exact Finset.sum_congr rfl (fun i _ => hEq _ _)
  change |(∑ i,∑ j,B (G₂ i j (D j u)) (D i u))+(∑ i,B (G₁ i (D i u)) u)+B (G₀ u) u| ≤ _
  rw [hSum₂,hSum₁,hEq (G₀ u) u,← integral_add hS₂ hS₁]
  have hS₂₁ : Integrable (fun x => (∑ i,∑ j,q₂ i j x)+(∑ i,q₁ i x)) vol := hS₂.add hS₁
  change |(∫ x,(∑ i,∑ j,q₂ i j x)+(∑ i,q₁ i x) ∂vol)+(∫ x,q₀ x ∂vol)| ≤ _
  rw [← integral_add hS₂₁ hS₀]
  apply abs_integral_weighted_trace_error_le vol hq he
  filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
  obtain ⟨E₂,E₁,E₀,hE₂,hE₁,hE₀,hF₂,hF₁,hF₀⟩ := hFiber x hx
  let h (i : I dim) := smoothSupportedTraceFiberL x (D i u)
  let f := smoothSupportedTraceFiberL x u
  let b₂ (i j : I dim) := ⟪smoothSphereTraceL2 hn (E₂ i j (h j)),smoothSphereTraceL2 hn (h i)⟫_ℝ
  let b₁ (i : I dim) := ⟪smoothSphereTraceL2 hn (E₁ i (h i)),smoothSphereTraceL2 hn f⟫_ℝ
  let b₀ := ⟪smoothSphereTraceL2 hn (E₀ f),smoothSphereTraceL2 hn f⟫_ℝ
  have hQ : q x = μ x*((∑ i,∑ j,b₂ i j)+(∑ i,b₁ i)+b₀) := by
    simp only [q,q₂,q₁,q₀,H,smoothSupportedTraceL2,hF₂,hF₁,hF₀,b₂,b₁,b₀,h,f,
      Finset.mul_sum,mul_add]
  have hP := abs_weighted_trace_error_density_le hn f h E₂ E₁ E₀ (β x) C (hβ x hx) hC hE₂ hE₁ hE₀
  change |(∑ i,∑ j,b₂ i j)+(∑ i,b₁ i)+b₀| ≤
    ((dim:ℝ)^2+dim+1)*C*coordinateTraceEnergy hn β u x at hP
  rw [hQ,abs_mul,abs_of_nonneg (hμ₀ x hx)]
  exact ((mul_le_mul_of_nonneg_left hP (hμ₀ x hx)).trans_eq
    (by ring : _ = ((dim:ℝ)^2+dim+1)*C*(μ x*coordinateTraceEnergy hn β u x))).trans
    (mul_le_mul_of_nonneg_left (hEnergy x hx) (by positivity))

end CalderonN
