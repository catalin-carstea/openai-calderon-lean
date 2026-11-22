module

public import Proof.CalderonN.BundleTraceLinearity
public import Proof.CalderonN.TraceResidualBounds

import Proof.CalderonN.CrossProductWeak
import Mathlib.Tactic

/-! Adapted from `BundleTraceCalculus` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothNear_baseMul {Y : Set (X dim)} {γ : (MetricField dim)} {χ : (X dim) → ℝ} {v : (Field dim)}
    (hχ : ContDiff ℝ ∞ χ) (hv : smoothNear v (bundle Y γ)) :
    smoothNear (baseMul χ v) (bundle Y γ) := by
  have hχ' : ContDiff ℝ ∞ (fun p : (X dim) × (X dim) => Complex.ofReal (χ p.1)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)
  exact smoothNear_mul_fields ⟨univ,isOpen_univ,subset_univ _,hχ'.contDiffOn⟩ hv

theorem smoothNear_one_bundle (Y : Set (X dim)) (γ : (MetricField dim)) :
    smoothNear (1 : (Field dim)) (bundle Y γ) :=
  ⟨univ,isOpen_univ,subset_univ _,contDiffOn_const⟩

section TraceRules
variable {Y : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {e : (Frame dim)}
  {r : (X dim) → ℝ} {A : (TraceAdjoint dim)}
  (hγ : SmoothMetric univ γ) (hE : ContDiff ℝ ∞ E) (hr : ContDiff ℝ ∞ r)
  (hDir : Dirichlet Y γ g E r)
  (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
  (hA : IsMovingTraceAdjoint Y γ g e E r A)

include hγ hE hr hDir he hA

theorem traceDerivative_congr_on_bundle (hY : IsOpen Y) {u v : (Field dim)}
    (hu : smoothNear u (bundle Y γ)) (hv : smoothNear v (bundle Y γ))
    (h : EqOn u v (bundle Y γ)) (i : (I dim)) :
    EqOn (traceDerivative γ A i u) (traceDerivative γ A i v) (bundle Y γ) := by
  have hAdj := adjointField_linear_combo_on_bundle hγ hE hr hDir he hA i hu hv hv
    (fun _ => 1) (fun _ => 0) (fun q hq => by simpa only [one_mul,zero_mul,add_zero] using h hq)
  apply eqOn_bundle_of_eqOn_frames he
  intro y hy w
  let q := (y,frameVector e y w)
  have hq : q ∈ bundle Y γ := ⟨hy,frameVector_mem_sphere γ e y (he y hy) w⟩
  have hH := horizontal_eq_of_eqOn_bundle hY hγ hy (he y hy) h w
    (differentiableAt_of_smoothNear_bundle hu hq) (differentiableAt_of_smoothNear_bundle hv hq) (axis i)
  change horizontal γ u q.1 q.2 (axis i) = horizontal γ v q.1 q.2 (axis i) at hH
  have hF := hAdj hq
  simp only [one_mul,zero_mul,add_zero] at hF
  change traceDerivative γ A i u q = traceDerivative γ A i v q
  simp only [traceDerivative,hH,hF]

theorem traceDerivative_baseMul_on_bundle {χ : (X dim) → ℝ} {u : (Field dim)}
    (hχ : ContDiff ℝ ∞ χ) (hu : smoothNear u (bundle Y γ)) (i : (I dim)) :
    EqOn (traceDerivative γ A i (baseMul χ u))
      (baseMul χ (traceDerivative γ A i u) + baseMul (coordDeriv i χ) u) (bundle Y γ) := by
  have hAdj := adjointField_linear_combo_on_bundle hγ hE hr hDir he hA i
    (smoothNear_baseMul hχ hu) hu hu (fun y => Complex.ofReal (χ y)) (fun _ => 0)
    (fun q _ => by simp only [baseMul,zero_mul,add_zero])
  intro q hq
  have h := hAdj hq
  simp only [zero_mul,add_zero] at h
  have hH := horizontal_baseMul_at γ (hχ.differentiable (by simp) q.1)
    (differentiableAt_of_smoothNear_bundle hu hq) i
  change traceDerivative γ A i (baseMul χ u) q =
    (baseMul χ (traceDerivative γ A i u) + baseMul (coordDeriv i χ) u) q
  simp only [traceDerivative,Pi.add_apply,hH,h,baseMul]
  ring

theorem traceDerivative_add_on_bundle {u v : (Field dim)}
    (hu : smoothNear u (bundle Y γ)) (hv : smoothNear v (bundle Y γ)) (i : (I dim)) :
    EqOn (traceDerivative γ A i (u+v))
      (traceDerivative γ A i u + traceDerivative γ A i v) (bundle Y γ) := by
  have hAdj := adjointField_linear_combo_on_bundle hγ hE hr hDir he hA i
    (smoothNear_add_fields hu hv) hu hv (fun _ => 1) (fun _ => 1)
    (fun q _ => by simp only [one_mul])
  intro q hq
  have h := hAdj hq
  simp only [one_mul] at h
  change adjointField A i (u+v) q = _ at h
  have hU := differentiableAt_of_smoothNear_bundle hu hq
  have hV := differentiableAt_of_smoothNear_bundle hv hq
  change traceDerivative γ A i (u+v) q =
    (traceDerivative γ A i u + traceDerivative γ A i v) q
  simp only [traceDerivative,Pi.add_apply,h,horizontal,fderiv_add hU hV,_root_.add_apply]
  ring

theorem traceDerivative_sub_on_bundle {u v : (Field dim)}
    (hu : smoothNear u (bundle Y γ)) (hv : smoothNear v (bundle Y γ)) (i : (I dim)) :
    EqOn (traceDerivative γ A i (u-v))
      (traceDerivative γ A i u - traceDerivative γ A i v) (bundle Y γ) := by
  have hAdj := adjointField_linear_combo_on_bundle hγ hE hr hDir he hA i
    (smoothNear_sub_fields hu hv) hu hv (fun _ => 1) (fun _ => -1)
    (fun q _ => by simp [sub_eq_add_neg])
  intro q hq
  have h := hAdj hq
  simp only [one_mul,neg_mul,← sub_eq_add_neg] at h
  change adjointField A i (u-v) q = _ at h
  have hU := differentiableAt_of_smoothNear_bundle hu hq
  have hV := differentiableAt_of_smoothNear_bundle hv hq
  change traceDerivative γ A i (u-v) q =
    (traceDerivative γ A i u - traceDerivative γ A i v) q
  simp only [traceDerivative,Pi.sub_apply,h,horizontal,fderiv_sub hU hV,_root_.sub_apply]
  ring

set_option maxHeartbeats 1550000 in
/-- The literal second-order trace commutator only requires smoothness of
the fields near the sphere bundle. -/
theorem movingTrace_baseMul_on_bundle (hY : IsOpen Y) (g₂ : (MetricField dim))
    {χ : (X dim) → ℝ} {u : (Field dim)} (hχ : ContDiff ℝ ∞ χ) (hu : smoothNear u (bundle Y γ)) :
    EqOn (movingTrace γ g₂ r A (baseMul χ u))
      (baseMul χ (movingTrace γ g₂ r A u) + traceCutoffResidual γ g₂ r A χ u) (bundle Y γ) := by
  let D (i : (I dim)) := traceDerivative γ A i
  have hgY := smoothMetric_restrict hγ (subset_univ Y)
  have hsD {v : (Field dim)} (hv : smoothNear v (bundle Y γ)) (i : (I dim)) :=
    smoothNear_traceDerivative hY hgY hA hv i
  have hχD (j : (I dim)) : ContDiff ℝ ∞ (coordDeriv j χ) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hD (j : (I dim)) := traceDerivative_baseMul_on_bundle hγ hE hr hDir he hA hχ hu j
  have hSecond (i j : (I dim)) : EqOn (D i (D j (baseMul χ u)))
      (baseMul χ (D i (D j u)) + baseMul (coordDeriv i χ) (D j u) +
        (baseMul (coordDeriv j χ) (D i u) + baseMul (coordDeriv i (coordDeriv j χ)) u))
      (bundle Y γ) := by
    have h₁ := smoothNear_baseMul hχ (hsD hu j)
    have h₂ := smoothNear_baseMul (hχD j) hu
    have hf := traceDerivative_congr_on_bundle hγ hE hr hDir he hA hY
      (hsD (smoothNear_baseMul hχ hu) j) (smoothNear_add_fields h₁ h₂) (hD j) i
    have ha := traceDerivative_add_on_bundle hγ hE hr hDir he hA h₁ h₂ i
    have hb := traceDerivative_baseMul_on_bundle hγ hE hr hDir he hA hχ (hsD hu j) i
    have hc := traceDerivative_baseMul_on_bundle hγ hE hr hDir he hA (hχD j) hu i
    intro q hq
    exact (hf hq).trans ((ha hq).trans (congrArg₂ (·+·) (hb hq) (hc hq)))
  intro q hq
  have h₁ (i : (I dim)) := hD i hq
  have h₂ (i j : (I dim)) := hSecond i j hq
  change movingTrace γ g₂ r A (baseMul χ u) q =
    (baseMul χ (movingTrace γ g₂ r A u) + traceCutoffResidual γ g₂ r A χ u) q
  simp only [movingTrace,D,Pi.add_apply,h₁,h₂,baseMul,traceCutoffResidual]
  simp only [mul_add,mul_sub,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring_nf
  all_goals ring

theorem movingTrace_sub_on_bundle (hY : IsOpen Y) (g₂ : (MetricField dim))
    {u v : (Field dim)} (hu : smoothNear u (bundle Y γ)) (hv : smoothNear v (bundle Y γ)) :
    EqOn (movingTrace γ g₂ r A (u-v))
      (movingTrace γ g₂ r A u - movingTrace γ g₂ r A v) (bundle Y γ) := by
  let D (i : (I dim)) := traceDerivative γ A i
  have hgY := smoothMetric_restrict hγ (subset_univ Y)
  have hsD {z : (Field dim)} (hz : smoothNear z (bundle Y γ)) (i : (I dim)) :=
    smoothNear_traceDerivative hY hgY hA hz i
  have hD (i : (I dim)) := traceDerivative_sub_on_bundle hγ hE hr hDir he hA hu hv i
  have hSecond (i j : (I dim)) : EqOn (D i (D j (u-v))) (D i (D j u)-D i (D j v)) (bundle Y γ) := by
    have heq := traceDerivative_congr_on_bundle hγ hE hr hDir he hA hY
      (hsD (smoothNear_sub_fields hu hv) j) (smoothNear_sub_fields (hsD hu j) (hsD hv j)) (hD j) i
    exact heq.trans (traceDerivative_sub_on_bundle hγ hE hr hDir he hA (hsD hu j) (hsD hv j) i)
  intro q hq
  have h₁ (i : (I dim)) := hD i hq
  have h₂ (i j : (I dim)) := hSecond i j hq
  change movingTrace γ g₂ r A (u-v) q = (movingTrace γ g₂ r A u - movingTrace γ g₂ r A v) q
  simp only [movingTrace,D,Pi.sub_apply,h₁,h₂]
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]
  ring_nf

end TraceRules

set_option maxHeartbeats 1500000 in
/-- For the actual smooth sphere fields, the same residual estimate
holds using only the protected adjoint and Dirichlet properties. -/
theorem traceNorm_cutoffDensity_le_of_bundle_bounds {Y : Set (X dim)} (hY : IsOpen Y) (d : (Data dim))
    (hγ : SmoothMetric univ d.γ) (hE : ContDiff ℝ ∞ d.expMap) (hr : ContDiff ℝ ∞ d.radius)
    (hDir : Dirichlet Y d.γ d.g₁ d.expMap d.radius)
    (he : ∀ y ∈ Y, ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (hA : IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius d.adjoint)
    (hVol : IntegrableOn (chartVolume d.γ) Y)
    {χ : (X dim) → ℝ} {ψ : (Field dim)} (hχ : ContDiff ℝ ∞ χ) (hψ : smoothNear ψ (bundle Y d.γ))
    (hEq : EqOn (movingTrace d.γ d.g₂ d.radius d.adjoint ψ) 0 (bundle Y d.γ))
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hconst : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
      ‖baseMul χ (movingTrace d.γ d.g₂ d.radius d.adjoint (1 : (Field dim)))
        (y,frameVector d.frame y w)‖ ≤ M₀)
    (hcomm : ∀ y ∈ Y, y ∈ tsupport (fderiv ℝ χ) → ∀ w : ↥(standardSphere dim),
      ‖traceCutoffResidual d.γ d.g₂ d.radius d.adjoint χ (ψ-1)
        (y,frameVector d.frame y w)‖ ≤ M₁) :
    traceNorm Y d (cutoffDensity χ ψ) ≤ (M₀+M₁) * Real.sqrt (∫ y in Y, chartVolume d.γ y) := by
  have hOne := smoothNear_one_bundle Y d.γ
  have hProd := movingTrace_baseMul_on_bundle hγ hE hr hDir he hA hY d.g₂ hχ
    (smoothNear_sub_fields hψ hOne)
  have hSub := movingTrace_sub_on_bundle hγ hE hr hDir he hA hY d.g₂ hψ hOne
  apply traceNorm_le_of_pointwise d _ (add_nonneg hM₀ hM₁) hY.measurableSet hVol
  intro y hy w
  let q := (y,frameVector d.frame y w)
  have hq : q ∈ bundle Y d.γ := ⟨hy,frameVector_mem_sphere d.γ d.frame y (he y hy) w⟩
  have h := hProd hq
  change movingTrace d.γ d.g₂ d.radius d.adjoint (cutoffDensity χ ψ) q =
    baseMul χ (movingTrace d.γ d.g₂ d.radius d.adjoint (ψ-1)) q +
      traceCutoffResidual d.γ d.g₂ d.radius d.adjoint χ (ψ-1) q at h
  have h' : baseMul χ (movingTrace d.γ d.g₂ d.radius d.adjoint (ψ-1)) q =
      -(baseMul χ (movingTrace d.γ d.g₂ d.radius d.adjoint (1:(Field dim))) q) := by
    have hs := hSub hq
    change movingTrace d.γ d.g₂ d.radius d.adjoint (ψ-1) q =
      movingTrace d.γ d.g₂ d.radius d.adjoint ψ q - movingTrace d.γ d.g₂ d.radius d.adjoint (1:(Field dim)) q at hs
    have hz := hEq hq
    unfold baseMul
    rw [hs,hz,Pi.zero_apply,zero_sub,mul_neg]
  have hR : ‖traceCutoffResidual d.γ d.g₂ d.radius d.adjoint χ (ψ-1) q‖ ≤ M₁ := by
    by_cases hS : y ∈ tsupport (fderiv ℝ χ)
    · exact hcomm y hy hS w
    · rw [traceCutoffResidual_eq_zero_off_differential_support _ _ _ _ _ _ q hS,norm_zero]
      exact hM₁
  change ‖movingTrace d.γ d.g₂ d.radius d.adjoint (cutoffDensity χ ψ) q‖ ≤ _
  rw [h,h']
  exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hconst y hy w) hR)

end CalderonN
