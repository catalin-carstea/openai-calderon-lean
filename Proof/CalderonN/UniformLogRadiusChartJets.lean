module

public import Proof.CalderonN.ProfileOrdinaryJetBound
public import Proof.CalderonN.UniformBackgroundChristoffelJets

import Proof.CalderonN.LocalMixedParameterJetCalculus
import Proof.CalderonN.ChartGeometry
import Mathlib.Tactic

/-! The protected covariant profile assumptions imply the uniform
ordinary derivatives of the logarithmic radius. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open ProfileCovariant
variable {dim : ℕ} [NeZero dim]

private theorem covJet_congrOn {U : Set (X dim)} (hU : IsOpen U) (g : MetricField dim)
    {f F : X dim → ℝ} (hEq : EqOn f F U) (n : ℕ) (I : Fin n → I dim) :
    EqOn (fun x => covJet g f n x I) (fun x => covJet g F n x I) U := by
  induction n with
  | zero => exact hEq
  | succ n ih =>
    intro x hx
    change covJet g f (n+1) x I = covJet g F (n+1) x I
    rw [covJet.eq_def,covJet.eq_def]
    change coordDeriv (I 0) (fun y => covJet g f n y (Fin.tail I)) x - _ =
      coordDeriv (I 0) (fun y => covJet g F n y (Fin.tail I)) x - _
    rw [eqOn_coordDeriv hU (ih (Fin.tail I)) (I 0) hx]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact congrArg (christoffel g x b (I 0) (I a.succ) * ·) (ih (Function.update (Fin.tail I) a b) hx)

theorem uniform_background_logRadius_chart_jets {Y Ω : Set (X dim)} (hY : IsOpen Y)
    (hΩ : IsOpen Ω) (hsub : Y ⊆ Ω) {m : ℕ} (N : ℕ) (hN8 : N ≤ 8) (hm : N+1 ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g g₁ g₂ : MetricField dim) (e : Frame dim),Background Ω K M g g₁ g₂ e →
      ∀ (r : X dim → ℝ) (floor c₀ : ℝ), 1 ≤ floor → Profile Y g e r floor c₀ Cj →
      ∀ x ∈ Y,∀ n ≤ N,1 ≤ n →
        ‖iteratedFDeriv ℝ n (fun y => Real.log (r y)) x‖ ≤ C*(beta g r x)^n := by
  obtain ⟨G,hG,hΓ⟩ := uniform_background_christoffel_jet_budget hΩ N hm K M hK
  let G₀ := (N.factorial:ℝ)*G
  have hG₀ : 0 ≤ G₀ := by dsimp only [G₀]; positivity
  let J := 1+∑ j : Fin 9,|Cj j|
  let A := (1+(dim:ℝ)*Real.sqrt K)^N*J
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let D := coordinateCoefficientGrowth N G₀
  have hD : 0 ≤ D := by dsimp only [D,coordinateCoefficientGrowth]; positivity
  let B := profileChartJetGrowth dim A D N
  have hB : 0 ≤ B := profileChartJetGrowth_nonneg A D hA hD N
  let C := (1+(dim:ℝ))^N*B
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro g g₁ g₂ e hbg r floor c₀ hFloor hProfile x hx
  let f (y : X dim) := Real.log (r y)
  let β := beta g r x
  have hβ : 1 ≤ β := hFloor.trans (hProfile.2 x hx).2.1
  have hf : ContDiffOn ℝ ∞ f Y := hProfile.1.log (fun y hy => (hProfile.2 y hy).1.ne')
  obtain ⟨F,hF,hFf⟩ := exists_global_smooth_germ_of_open f hY hf hx
  have hΓ₀ (k i j : I dim) : ∃ U : X dim → ℝ,ContDiff ℝ ∞ U ∧ U =ᶠ[𝓝 x] (fun y => christoffel g y k i j) :=
    exists_global_smooth_germ_of_open _ hΩ (hbg.1.contDiffOn_christoffel hΩ hK k i j) (hsub hx)
  choose Γ hΓsmooth hΓEq using hΓ₀
  let L := ContinuousLinearMap.snd ℝ ℝ (X dim)
  let cΓ (k i j : I dim) (p : ℝ × X dim) := Γ k i j p.2
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.2‖ ≤ 1*‖p‖
    simpa only [one_mul] using norm_snd_le p
  have hcΓ (k i j : I dim) : ContDiff ℝ ∞ (cΓ k i j) := (hΓsmooth k i j).comp contDiff_snd
  have hΓJ (k i j : I dim) : LocalSmoothJetBudget (cΓ k i j) (0,x) N G₀ := by
    have hh := hΓ g g₁ g₂ e hbg x (hsub hx) k i j
    have hExt : LocalSmoothJetBudget (Γ k i j) x N G :=
      ⟨(hΓsmooth k i j).contDiffAt,fun n hn => ((hΓEq k i j).iteratedFDeriv ℝ n).eq_of_nhds.symm ▸ hh.bound n hn⟩
    have hLift := hExt.linear_precomp L (0,x)
    change LocalSmoothJetBudget (Γ k i j ∘ L) (0,x) N ((N.factorial:ℝ)*G)
    simpa only [max_eq_left hL,one_pow,mul_one] using hLift
  have hΓAll : ∀ᶠ y : X dim in 𝓝 x,∀ k i j : I dim, Γ k i j y = christoffel g y k i j :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hΓEq k i j
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp (hFf.and hΓAll)
  have hCov (n : ℕ) (hn : n ≤ N) (hpos : 1 ≤ n) (I : Fin n → I dim) :
      |covariantCoordinateJet cΓ F 0 n x I| ≤ A*β^n := by
    have hOn : EqOn F f U := fun _ hy => (hUsub hy).1
    have hCF := covJet_congrOn hU g hOn n I hxU
    have hCG := covJet_eq_on hU g cΓ 0 (fun y hy k i j => (hUsub hy).2 k i j) F n I hxU
    dsimp only at hCF hCG
    rw [← hCG,hCF]
    have h₁ := abs_covJet_chart_le hbg.1 (hsub hx) (hbg.2.2.2.2.2.2.2 x (hsub hx)) f n I
    have h₂ := (hProfile.2 x hx).2.2.2 ⟨n,by omega⟩ hpos
    have hJle : Cj ⟨n,by omega⟩ ≤ J := by
      exact (le_abs_self _).trans ((Finset.single_le_sum (f:=fun j : Fin 9 => |Cj j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ ⟨n,by omega⟩)).trans (le_add_of_nonneg_left zero_le_one))
    have hBnd : ((dim:ℝ)*Real.sqrt K)^n ≤ (1+(dim:ℝ)*Real.sqrt K)^N := by
      have hMul : 0 ≤ (dim:ℝ)*Real.sqrt K := by positivity
      refine (pow_le_pow_left₀ hMul (le_add_of_nonneg_left zero_le_one) _).trans ?_
      exact pow_le_pow_right₀ (le_add_of_nonneg_right hMul) hn
    apply h₁.trans
    calc
      _ ≤ ((dim:ℝ)*Real.sqrt K)^n*(Cj ⟨n,by omega⟩*β^n) :=
        mul_le_mul_of_nonneg_left h₂ (by positivity)
      _ ≤ ((dim:ℝ)*Real.sqrt K)^n*(J*β^n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJle (by positivity)) (by positivity)
      _ ≤ A*β^n := by
        simpa only [A,mul_assoc] using mul_le_mul_of_nonneg_right hBnd (by positivity : 0 ≤ J*β^n)
  intro n hn hpos
  have hComp (I : Fin n → I dim) :
      |iteratedFDeriv ℝ n F x (fun j => axis (I j))| ≤ B*β^n := by
    apply (abs_coordinatePartialJet_le_of_covariant_bounds cΓ hcΓ (0,x) N G₀ hG₀ hΓJ F hF β A hβ
      hA hCov n hn hpos I).trans
    exact mul_le_mul_of_nonneg_right (profileChartJetGrowth_mono (dim:=dim) A D hA hD hn)
      (pow_nonneg (zero_le_one.trans hβ) _)
  rw [← (hFf.iteratedFDeriv ℝ n).eq_of_nhds]
  refine (norm_multilinear_le_of_chart_components (iteratedFDeriv ℝ n F x) (B*β^n)
    (by positivity) hComp).trans ?_
  have hDim : (dim:ℝ)^n ≤ (1+(dim:ℝ))^N :=
    (pow_le_pow_left₀ (by positivity) (le_add_of_nonneg_left zero_le_one) _).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg dim)) hn)
  simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_right hDim (by positivity : 0 ≤ B*β^n)

end CalderonN
