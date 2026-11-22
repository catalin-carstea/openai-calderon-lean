module

public import Proof.CalderonN.UniformMetricInverseEntryJets
public import Proof.CalderonN.TraceCoordinateModel
public import Proof.CalderonN.MovingTraceCoordinateSquare

import Proof.CalderonN.UniformLogRadiusChartJets
import Proof.CalderonN.UniformCanonicalFrameJets
import Proof.CalderonN.SmallJetBounds
import Proof.CalderonN.CurvatureOperatorBounds
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! Pointwise scalar bounds in the ordinary coordinate expression for
the lower-order part of the physical trace operator. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem norm_smooth_frameCoordinates_jet
    {g : MetricField dim} {e : Frame dim} {x : X dim} (a i : I dim)
    (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hG : ∀ i j,LocalSmoothJetBudget (fun y => g y i j) x 1 L)
    (hE : LocalSmoothJetBudget (fun y => e y a) x 1 C) :
    LocalSmoothJetBudget (traceFrameCoordinate g e a i) x 1
      ((dim:ℝ)*(2*‖ContinuousLinearMap.mul ℝ ℝ‖*L*C)) := by
  have he : traceFrameCoordinate g e a i = fun y => ∑ j : I dim,g y i j*e y a j := by
    funext y
    rw [traceFrameCoordinate,frameCoordinatesL_apply]
    change metricPair g y (axis i) (e y a) = _
    exact metricPair_axis_left g y (e y a) i
  rw [he]
  have h (j : I dim) : LocalSmoothJetBudget (fun y => g y i j*e y a j) x 1
      (2*‖ContinuousLinearMap.mul ℝ ℝ‖*L*C) := by
    let p := EuclideanSpace.proj (𝕜:=ℝ) j
    have h₁ : LocalSmoothJetBudget (fun y => e y a j) x 1 C :=
      (hE.linear_postcomp p).enlarge
        ((mul_le_mul_of_nonneg_right (norm_euclidean_proj_le_one j) hC).trans_eq (one_mul _))
    have h₂ := (hG i j).bilinear h₁ (ContinuousLinearMap.mul ℝ ℝ)
    change LocalSmoothJetBudget (fun y => g y i j*e y a j) x 1
      ((2:ℝ)^1*‖ContinuousLinearMap.mul ℝ ℝ‖*L*C) at h₂
    simpa only [pow_one] using h₂
  have hh := LocalSmoothJetBudget.finite_sum Finset.univ
    (fun j : I dim => fun y => g y i j*e y a j) (fun _ => 2*‖ContinuousLinearMap.mul ℝ ℝ‖*L*C) (fun j _ => h j)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

theorem uniform_traceCoordinate_scalar_bounds {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ floor ≥ 1,∀ ε ≤ 1,∀ d : Data dim,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y a,d.frame y a = smoothMetricFrame (d.γ y) a) →
      ∀ x ∈ Y,
        (∀ i j, |principal d.γ d.g₂ x i j| ≤ C) ∧
        (∀ i, |traceCoordinateDrift d.γ d.g₂ i x| ≤ C) ∧
        (∀ i a, |traceFrameCoordinate d.γ d.frame a i x| ≤ C) ∧
        (∀ i j a, |coordDeriv i (traceFrameCoordinate d.γ d.frame a j) x| ≤ C) ∧
        (∀ i a b, |frameConnectionCoefficient d.γ d.frame x (axis i) a b| ≤ C) ∧
        (∀ i, |traceCoordinateLogGradient d.radius i x| ≤ C*beta d.γ d.radius x) := by
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨F,hF,hFrame⟩ := uniform_canonical_metric_frame_jets (dim:=dim) K hKp M
  obtain ⟨G,hG,hΓ⟩ := uniform_background_christoffel_jet_budget hΩ 0 (by omega) K M hKp
  obtain ⟨Q,hQ,hI⟩ := uniform_metric_inverse_entry_jet_budget hΩ 0 (Nat.zero_le _) K M hKp
  obtain ⟨L,hL,hLog⟩ := uniform_background_logRadius_chart_jets hY hΩ hSub 1 (by decide) hm K M Cj hKp
  let A := backgroundAllMetricJetBudget M
  have hA := backgroundAllMetricJetBudget_ge_one M
  have hA₀ := zero_le_one.trans hA
  have hF₀ := zero_le_one.trans hF
  let c := (dim:ℝ)*(2*‖ContinuousLinearMap.mul ℝ ℝ‖*A*F)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  let Γ := (dim:ℝ)^2*A*(F+(dim:ℝ)^3*G*F)*F
  have hΓ₀ : 0 ≤ Γ := by dsimp only [Γ]; positivity
  let D := K+(dim:ℝ)^2*(Q+1)*G
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let C := 1+(Q+1+D+c+Γ+L)
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC,?_⟩
  intro floor hf ε hs d hd hCan x hx
  have hxΩ := hSub hx
  have hβ := hf.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hr := (hd.2.2.2.2.1.2 x hx).1
  have hrε : d.radius x ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 x hx).2
  have hγ (k : Fin (m+1)) (i j : I dim) (y : X dim) (hy : y ∈ Ω) :=
    hd.1.2.2.2.2.1 d.γ (by simp) k i j y hy
  have hQ₁ (i j : I dim) : |principal d.γ d.g₂ x i j| ≤ Q+1 := by
    have hInv : |(d.γ x)⁻¹ i j| ≤ Q := (hI d.γ hd.1.1 hγ x hxΩ i j).value_norm_le
    have hSmall := (abs_principal_sub_inverse_entry_le_smallJet d.γ d.g₂ x i j).trans
      ((hd.2.2.2.2.2 x hx).1.trans (show ε*d.radius x ≤ 1 from
        (mul_le_mul hs (hrε.trans hs) hr.le zero_le_one).trans_eq (one_mul _)))
    calc
      |principal d.γ d.g₂ x i j| =
          |(d.γ x)⁻¹ i j+(principal d.γ d.g₂ x i j-(d.γ x)⁻¹ i j)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hInv hSmall)
  have hΓ₁ (k i j : I dim) : |christoffel d.γ x k i j| ≤ G :=
    (hΓ d.γ d.g₁ d.g₂ d.frame hd.1 x hxΩ k i j).value_norm_le
  have hDrift (k : I dim) : |traceCoordinateDrift d.γ d.g₂ k x| ≤ D := by
    let t := ∑ i : I dim,∑ j : I dim,principal d.γ d.g₂ x i j*christoffel d.γ x k i j
    have ht : |t| ≤ (dim:ℝ)^2*(Q+1)*G := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ =>
        Finset.abs_sum_le_sum_abs _ _)).trans ?_)
      calc
        _ ≤ ∑ _i : I dim,∑ _j : I dim,(Q+1)*G := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul (hQ₁ i j) (hΓ₁ k i j) (abs_nonneg _) (by positivity)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
    change |drift d.γ d.g₂ x k-t| ≤ D
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans (add_le_add (hd.1.2.2.2.2.2.1 x hxΩ k) (by rwa [abs_neg]))
  have he (a : I dim) : LocalSmoothJetBudget (fun y => d.frame y a) x 1 F := by
    refine ⟨(hd.1.2.2.2.2.2.2.1 a).contDiffAt (hΩ.mem_nhds hxΩ),?_⟩
    intro n hn
    simp_rw [hCan]
    exact hFrame hΩ hd.1.1 hγ x hxΩ a n (by omega)
  have hg (i j : I dim) : LocalSmoothJetBudget (fun y => d.γ y i j) x 1 A := by
    refine ⟨(hd.1.1.1 i j).contDiffAt (hΩ.mem_nhds hxΩ),?_⟩
    intro n hn
    exact (hγ ⟨n,by omega⟩ i j x hxΩ).trans ((le_abs_self _).trans (abs_metricJet_le_all_budget M _))
  have hcF (a i : I dim) : LocalSmoothJetBudget (traceFrameCoordinate d.γ d.frame a i) x 1 c :=
    norm_smooth_frameCoordinates_jet a i A F hA₀ hF₀ hg (he a)
  have hGConn := connectionBilinear_norm_of_entry_bound d.γ x G (zero_le_one.trans hG) hΓ₁
  have hConn (i a : I dim) : ‖covariantFrameVector d.γ d.frame x (axis i) a‖ ≤ F+(dim:ℝ)^3*G*F := by
    unfold covariantFrameVector
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have hd' := (he a).bound 1 (by decide)
      rw [norm_iteratedFDeriv_one] at hd'
      exact ((fderiv ℝ (fun y => d.frame y a) x).le_opNorm _).trans
        (by simpa only [norm_axis,mul_one] using hd')
    · rw [← connectionBilinear_apply]
      have hL₁ := ((connectionBilinear d.γ x).le_opNorm (axis i)).trans
        (by simpa only [norm_axis,mul_one] using hGConn)
      exact (((connectionBilinear d.γ x) (axis i)).le_opNorm _).trans
        (mul_le_mul hL₁ (he a).value_norm_le (norm_nonneg _) (by positivity))
  refine ⟨fun i j => (hQ₁ i j).trans (by dsimp only [C]; linarith),
    fun i => (hDrift i).trans (by dsimp only [C]; linarith),
    fun i a => (hcF a i).value_norm_le.trans (by dsimp only [C]; linarith),?_,?_,?_⟩
  · intro i j a
    have h := (hcF a j).bound 1 (by decide)
    rw [norm_iteratedFDeriv_one] at h
    have h' := ((fderiv ℝ (traceFrameCoordinate d.γ d.frame a j) x).le_opNorm (axis i)).trans
      (by simpa only [norm_axis,mul_one] using h)
    exact h'.trans (by dsimp only [C]; linarith)
  · intro i a b
    have hM := metricPair_abs_le_of_entry_bound d.γ x A hA₀ (fun i j => (hg i j).value_norm_le)
      (covariantFrameVector d.γ d.frame x (axis i) a) (d.frame x b)
    exact (hM.trans (by dsimp only [Γ]; gcongr; exact hConn i a; exact (he b).value_norm_le : _ ≤ Γ)).trans
      (by dsimp only [C]; linarith)
  · intro i
    have h := hLog d.γ d.g₁ d.g₂ d.frame hd.1 d.radius floor c₀ hf hd.2.2.2.2.1 x hx 1 le_rfl le_rfl
    rw [norm_iteratedFDeriv_one,pow_one] at h
    have h' := ((fderiv ℝ (fun y => Real.log (d.radius y)) x).le_opNorm (axis i)).trans
      (by simpa only [norm_axis,mul_one] using h)
    exact h'.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
      (zero_le_one.trans hβ))

end CalderonN
