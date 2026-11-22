module

public import Proof.CalderonN.JointCoefficientSmoothness
public import Proof.CalderonN.StrictRankOne
import Mathlib.Tactic

/-! Adapted from `Calderon/ActualCompactParameterStrictWeightCarleman.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

namespace CalderonN.Carleman.Strict
open CalderonN.Elliptic.Strict (JointSmooth jointSmooth_pd jointSmooth_add jointSmooth_mul
  jointSmooth_const_mul jointSmooth_sum jointSmooth_divV jointSmooth_Lop jointSmooth_slice)

variable {dim : ℕ} [NeZero dim]

theorem continuous_quad_form {P : Type*} [TopologicalSpace P] {A : P → Fin dim → Fin dim → ℝ}
    (hA : Continuous A) :
    Continuous (fun p : P × (Fin dim → ℝ) => ∑ i, ∑ k, A p.1 i k * p.2 i * p.2 k) := by
  fun_prop

theorem continuous_E1_form {P : Type*} [TopologicalSpace P] {A : P → Fin dim → Fin dim → ℝ}
    {dB : P → Fin dim → Fin dim → ℝ} {dA : P → Fin dim → Fin dim → Fin dim → ℝ} {b : P → Fin dim → ℝ}
    (hA : Continuous A) (hdB : Continuous dB) (hdA : Continuous dA) (hb : Continuous b) :
    Continuous (fun p : P × (Fin dim → ℝ) =>
      4 * ∑ i, ∑ j, ∑ l, A p.1 i l * p.2 l * dB p.1 i j * p.2 j -
        2 * ∑ j, b p.1 j * ∑ i, ∑ k, dA p.1 j i k * p.2 i * p.2 k) := by
  fun_prop

/-- The strict phase is unchanged; all constants precede the compact family parameter. -/
theorem strict_weight_carleman_of_joint_coordinate_strictness
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → Fin dim → Fin dim → (CalderonN.X dim) → ℝ) (psi : E → (CalderonN.X dim) → ℝ)
    (ha : ∀ i k, JointSmooth fun P => a P i k) (hpsi : JointSmooth psi)
    (hsymm : ∀ P i k, a P i k = a P k i)
    (Q : Set (E×(CalderonN.X dim))) (hQ : IsCompact Q) (m : E → ℝ) (hm : Continuous m)
    (htan : ∀ z ∈ Q, ∀ xi : Fin dim → ℝ, xi ≠ 0 →
      ∑ j, phaseField (a z.1) (psi z.1) j z.2 * xi j = 0 →
      0 < Mgrad (a z.1) (phaseField (a z.1) (psi z.1)) z.2 xi + 4*m z.1*quad (a z.1) z.2 xi)
    (hnor : ∀ z ∈ Q, 0 < 2 * ∑ j, phaseField (a z.1) (psi z.1) j z.2 *
      pd j (phaseNorm (a z.1) (psi z.1)) z.2 - 4*m z.1*phaseNorm (a z.1) (psi z.1) z.2) :
    ∃ C tau0 : ℝ, 0 < C ∧ 1 ≤ tau0 ∧ ∀ P : E, ∀ tau : ℝ, tau0 ≤ tau →
      ∀ w : (CalderonN.X dim) → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ {x | (P,x)∈Q} →
      tau * (∫ x, ∑ i, pd i (fun y => Real.exp (tau*psi P y)*w y) x ^ 2) +
        tau^3*(∫ x, (Real.exp (tau*psi P x)*w x)^2) ≤
        C * ∫ x, Real.exp (2*(tau*psi P x))*Lop (a P) w x ^ 2 := by
  let W : E → Fin dim → (CalderonN.X dim) → ℝ := fun P => phaseField (a P) (psi P)
  let N : E → (CalderonN.X dim) → ℝ := fun P => phaseNorm (a P) (psi P)
  have hW : ∀ j, JointSmooth fun P => W P j := by
    intro j
    exact jointSmooth_sum (F:=fun k P x => a P j k x * pd k (psi P) x)
      (fun k => jointSmooth_mul (ha j k) (jointSmooth_pd hpsi k))
  have hN : JointSmooth N := by
    exact jointSmooth_sum (F:=fun i P x => ∑ k, a P i k x*pd i (psi P) x*pd k (psi P) x)
      (fun i => jointSmooth_sum (F:=fun k P x => a P i k x*pd i (psi P) x*pd k (psi P) x)
        (fun k => jointSmooth_mul (jointSmooth_mul (ha i k) (jointSmooth_pd hpsi i)) (jointSmooth_pd hpsi k)))
  have hac : ∀ i k, Continuous (fun z:E×(CalderonN.X dim) => a z.1 i k z.2) := fun i k => (ha i k).continuous
  have hdac : ∀ j i k, Continuous (fun z:E×(CalderonN.X dim) => pd j (a z.1 i k) z.2) :=
    fun j i k => (jointSmooth_pd (ha i k) j).continuous
  have hWc : ∀ j, Continuous (fun z:E×(CalderonN.X dim) => W z.1 j z.2) := fun j => (hW j).continuous
  have hdWc : ∀ i j, Continuous (fun z:E×(CalderonN.X dim) => pd i (W z.1 j) z.2) :=
    fun i j => (jointSmooth_pd (hW j) i).continuous
  have hmc : Continuous (fun z:E×(CalderonN.X dim) => m z.1) := hm.comp continuous_fst
  have hForm : Continuous (fun z:(E×(CalderonN.X dim))×(Fin dim→ℝ) =>
      Mgrad (a z.1.1) (W z.1.1) z.1.2 z.2+4*m z.1.1*quad (a z.1.1) z.1.2 z.2) := by
    have hAj : Continuous (fun z:E×(CalderonN.X dim) => fun i k => a z.1 i k z.2) :=
      continuous_pi fun i => continuous_pi fun k => hac i k
    have hDWj : Continuous (fun z:E×(CalderonN.X dim) => fun i j => pd i (W z.1 j) z.2) :=
      continuous_pi fun i => continuous_pi fun j => hdWc i j
    have hdAj : Continuous (fun z:E×(CalderonN.X dim) => fun j i k => pd j (a z.1 i k) z.2) :=
      continuous_pi fun j => continuous_pi fun i => continuous_pi fun k => hdac j i k
    have hWj : Continuous (fun z:E×(CalderonN.X dim) => fun j => W z.1 j z.2) :=
      continuous_pi fun j => hWc j
    exact (continuous_E1_form hAj hDWj hdAj hWj).add
      ((continuous_const.mul (hm.comp continuous_fst.fst)).mul (continuous_quad_form hAj))
  have hLin : Continuous (fun z:(E×(CalderonN.X dim))×(Fin dim→ℝ) => ∑ j,W z.1.1 j z.1.2*z.2 j) := by

    fun_prop
  obtain ⟨D,alpha,hD,halpha,hcoef⟩ := uniform_rank_one_coercivity_on_compact_parameter_space hQ
    (fun z xi => Mgrad (a z.1) (W z.1) z.2 xi+4*m z.1*quad (a z.1) z.2 xi)
    (fun z xi => ∑ j,W z.1 j z.2*xi j) hForm hLin
    (by intro z c xi; rw [Mgrad_smul, quad_smul]; ring)
    (by intro z c xi; exact lin_smul _ _ _ _) htan
  have hdNc : ∀ j, Continuous (fun z:E×(CalderonN.X dim) => pd j (N z.1) z.2) :=
    fun j => (jointSmooth_pd hN j).continuous
  have hNc : Continuous (fun z:E×(CalderonN.X dim) => N z.1 z.2) := hN.continuous
  have hZ : Continuous (fun z:E×(CalderonN.X dim) => 2*∑ j,W z.1 j z.2*pd j (N z.1) z.2-4*m z.1*N z.1 z.2) := by
    fun_prop
  obtain ⟨beta,hbeta,hZbound⟩ := exists_pos_lower_of_compact hQ hZ.continuousOn hnor
  have hDiv : JointSmooth (fun P => divV (W P)) := jointSmooth_divV hW
  obtain ⟨R0,hR⟩ := hQ.exists_bound_of_continuousOn
    (jointSmooth_Lop ha hDiv).continuous.continuousOn
  obtain ⟨d0,hd⟩ := hQ.exists_bound_of_continuousOn hDiv.continuous.continuousOn
  obtain ⟨m0,hm0⟩ := hQ.exists_bound_of_continuousOn hmc.continuousOn
  let M : ℝ := max m0 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  let c : ℝ := min alpha (beta/2)
  have hc : 0 < c := lt_min halpha (half_pos hbeta)
  refine ⟨1/c,max (max 1 D) (max (32*M^2/beta) (4*(R0+D*d0^2/2)/beta)),
    one_div_pos.mpr hc, (le_max_left 1 D).trans (le_max_left _ _),?_⟩
  intro P tau htau w hw hwc hsupp
  have htau1 : 1 ≤ tau := ((le_max_left 1 D).trans (le_max_left _ _)).trans htau
  have htauD : D ≤ tau := ((le_max_right 1 D).trans (le_max_left _ _)).trans htau
  have htauM : 32*M^2 ≤ beta*tau := by
    have h := ((le_max_left (32*M^2/beta) (4*(R0+D*d0^2/2)/beta)).trans (le_max_right (max 1 D) _)).trans htau
    rw [div_le_iff₀ hbeta] at h
    linarith
  have htauR : 4*(R0+D*d0^2/2) ≤ beta*tau := by
    have h := ((le_max_right (32*M^2/beta) (4*(R0+D*d0^2/2)/beta)).trans (le_max_right (max 1 D) _)).trans htau
    rw [div_le_iff₀ hbeta] at h
    linarith
  by_cases hFiber : {x:(CalderonN.X dim) | (P,x)∈Q}.Nonempty
  · obtain ⟨x0,hx0⟩ := hFiber
    have hmBound : |m P| ≤ M := by
      have h := hm0 (P,x0) hx0
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    have hmSq : (m P)^2 ≤ M^2 := (sq_abs (m P)) ▸ pow_le_pow_left₀ (abs_nonneg _) hmBound 2
    have h := unchanged_phase_estimate_of_coefficient_bounds
      (fun i k => jointSmooth_slice (ha i k) P) (hsymm P) (jointSmooth_slice hpsi P)
      hw hwc {x | (P,x)∈Q} hsupp (m P) alpha beta D R0 d0 hbeta hD
      (fun x hx xi => hcoef (P,x) hx xi) (fun x hx => hZbound (P,x) hx)
      (fun x hx => by simpa only [Real.norm_eq_abs, CalderonN.Elliptic.Lop, CalderonN.Carleman.Lop,
        CalderonN.Elliptic.pd, CalderonN.Carleman.pd, CalderonN.coordDeriv, CalderonN.axis] using hR (P,x) hx)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hd (P,x) hx)
      tau htau1 htauD (by nlinarith only [htauM,hmSq]) htauR
    have hG0 : 0 ≤ ∫ x, ∑ i,pd i (fun y => Real.exp (tau*psi P y)*w y) x^2 :=
      integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hV0 : 0 ≤ ∫ x,(Real.exp (tau*psi P x)*w x)^2 := integral_nonneg fun x => sq_nonneg _
    have htau0 : 0 ≤ tau := by linarith
    have e1 : c*(tau*(∫ x,∑ i,pd i (fun y => Real.exp (tau*psi P y)*w y) x^2)) ≤
        alpha*tau*(∫ x,∑ i,pd i (fun y => Real.exp (tau*psi P y)*w y) x^2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) htau0) hG0
    have e2 : c*(tau^3*(∫ x,(Real.exp (tau*psi P x)*w x)^2)) ≤
        beta/2*tau^3*(∫ x,(Real.exp (tau*psi P x)*w x)^2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg htau0 3)) hV0
    rw [div_mul_eq_mul_div,one_mul,le_div_iff₀ hc]
    linarith
  · have hEmpty : {x:(CalderonN.X dim) | (P,x)∈Q}=∅ := Set.not_nonempty_iff_eq_empty.mp hFiber
    have hw0 : w=0 := by
      funext x
      by_contra hne
      have hx : x∈tsupport w := subset_tsupport w (show w x ≠ 0 by simpa only [Pi.zero_apply] using hne)
      have h := hsupp hx
      rw [hEmpty] at h
      exact h
    subst w
    have hRhs : 0 ≤ (1/c)*∫ x:(CalderonN.X dim),Real.exp (2*(tau*psi P x))*Lop (a P) (0:(CalderonN.X dim)→ℝ) x^2 :=
      mul_nonneg (one_div_nonneg.mpr hc.le)
        (integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    simpa [pd_const] using hRhs

end CalderonN.Carleman.Strict
