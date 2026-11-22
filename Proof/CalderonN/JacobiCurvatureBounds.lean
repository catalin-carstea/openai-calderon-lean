module

public import Proof.CalderonN.JacobiAcceleration

import Proof.CalderonN.DilationConnection
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem connection_smul_left (g : (MetricField dim)) (x u v : (X dim)) (a : ℝ) :
    connection g x (a • u) v = a • connection g x u v := by
  ext k
  simp only [connection, PiLp.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem connection_smul_right (g : (MetricField dim)) (x u v : (X dim)) (b : ℝ) :
    connection g x u (b • v) = b • connection g x u v := by
  ext k
  simp only [connection, PiLp.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem connectionDerivative_smul (g : (MetricField dim)) (x d u v : (X dim)) (a b c : ℝ) :
    connectionDerivative g x (a • d) (b • u) (c • v) =
      (a * b * c) • connectionDerivative g x d u v := by
  ext k
  simp only [connectionDerivative, PiLp.smul_apply, map_smul, smul_eq_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem jacobiCurvatureTerm_smul (g : (MetricField dim)) (x v J : (X dim)) (a b : ℝ) :
    jacobiCurvatureTerm g x (a • v) (b • J) =
      (a^2*b) • jacobiCurvatureTerm g x v J := by
  unfold jacobiCurvatureTerm
  simp only [connectionDerivative_smul, connection_smul_left, connection_smul_right, smul_smul,
    smul_add, smul_sub]
  rw [show a*a*b = a^2*b by ring, show b*a*a = a^2*b by ring,
    show b*(a*a) = a^2*b by ring]

private theorem continuous_connectionCoefficients {P : Type*} [TopologicalSpace P]
    {Γ : (I dim) → (I dim) → (I dim) → P → ℝ} (hΓ : ∀ k i j, Continuous (Γ k i j))
    {v w : P → (X dim)} (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun p : P => (WithLp.toLp 2 fun k => ∑ i, ∑ j, Γ k i j p * v p i * w p j) : P → (X dim)) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : (I dim) => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro k
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((hΓ k i j).mul ((EuclideanSpace.proj i).continuous.comp hv)).mul
    ((EuclideanSpace.proj j).continuous.comp hw)

set_option maxHeartbeats 600000 in
private theorem continuous_jacobiCurvatureTerm
    {γ : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hpos : ∀ a x, (γ a x).PosDef) :
    Continuous (fun p : (ℝ × (X dim)) × ((X dim) × (X dim)) => jacobiCurvatureTerm (γ p.1.1) p.1.2 p.2.1 p.2.2) := by
  let Γ (k i j : (I dim)) (q : ℝ × (X dim)) := christoffel (γ q.1) q.2 k i j
  have hΓ (k i j : (I dim)) : ContDiff ℝ ∞ (Γ k i j) :=
    contDiffOn_univ.mp (contDiffOn_christoffel_slice isOpen_univ
      (fun i j => (hγ i j).contDiffOn) (fun q _ => hpos q.1 q.2) k i j)
  have hDΓ (k i j : (I dim)) (q : ℝ × (X dim)) :
      fderiv ℝ (fun y => christoffel (γ q.1) y k i j) q.2 =
        (fderiv ℝ (Γ k i j) q).comp (ContinuousLinearMap.inr ℝ ℝ (X dim)) := by
    have hi : HasFDerivAt (fun y : (X dim) => (q.1,y)) (ContinuousLinearMap.inr ℝ ℝ (X dim)) q.2 :=
      (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
    have ho : HasFDerivAt (Γ k i j) (fderiv ℝ (Γ k i j) q) q :=
      ((hΓ k i j).differentiable (by simp) q).hasFDerivAt
    exact (ho.comp q.2 hi).fderiv
  let P := (ℝ × (X dim)) × ((X dim) × (X dim))
  have hconn {v w : P → (X dim)} (hv : Continuous v) (hw : Continuous w) :
      Continuous (fun p : P => connection (γ p.1.1) p.1.2 (v p) (w p)) :=
    continuous_connectionCoefficients (P := P) (Γ := fun k i j p => Γ k i j p.1)
      (fun k i j => (hΓ k i j).continuous.comp continuous_fst) hv hw
  have hdconn {d v w : P → (X dim)} (hd : Continuous d) (hv : Continuous v) (hw : Continuous w) :
      Continuous (fun p : P => connectionDerivative (γ p.1.1) p.1.2 (d p) (v p) (w p)) := by
    let A (k i j : (I dim)) (p : P) :=
      fderiv ℝ (fun y => christoffel (γ p.1.1) y k i j) p.1.2 (d p)
    have hA (k i j : (I dim)) : Continuous (A k i j) := by
      have hEq : A k i j = fun p : P => fderiv ℝ (Γ k i j) p.1 (0,d p) := by
        funext p
        change fderiv ℝ (fun y => christoffel (γ p.1.1) y k i j) p.1.2 (d p) = _
        rw [hDΓ k i j p.1]
        rfl
      rw [hEq]
      exact (((hΓ k i j).fderiv_right (m := ∞) (by simp)).continuous.comp
        continuous_fst).clm_apply (continuous_const.prodMk hd)
    exact continuous_connectionCoefficients (P := P) (Γ := A) hA hv hw
  have hv : Continuous (fun p : P => p.2.1) := continuous_fst.comp continuous_snd
  have hJ : Continuous (fun p : P => p.2.2) := continuous_snd.comp continuous_snd
  exact (((hdconn hv hv hJ).sub (hdconn hJ hv hv)).sub (hconn (hconn hv hv) hJ)).add
    (hconn hv (hconn hv hJ))

/-- A single curvature bound for all base points and all metric parameters
in a compact set. The velocity contributes exactly two powers of its norm. -/
theorem exists_uniform_jacobiCurvatureTerm_bound
    {γ : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hpos : ∀ a x, (γ a x).PosDef) {K : Set (ℝ × (X dim))} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ v J : (X dim),
      ‖jacobiCurvatureTerm (γ p.1) p.2 v J‖ ≤ C * ‖v‖^2 * ‖J‖ := by
  let S := sphere (0 : (X dim)) 1
  have hSS : IsCompact (S ×ˢ S) := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  obtain ⟨B,hB⟩ := (hK.prod hSS).exists_bound_of_continuousOn
    (continuous_jacobiCurvatureTerm hγ hpos).continuousOn
  let C := max B 0
  refine ⟨C,le_max_right _ _,fun p hp v J => ?_⟩
  by_cases hv : v = 0
  · have h := jacobiCurvatureTerm_smul (γ p.1) p.2 v J 0 1
    simp only [zero_smul, one_smul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at h
    simp [hv,h]
  by_cases hJ : J = 0
  · have h := jacobiCurvatureTerm_smul (γ p.1) p.2 v J 1 0
    simp only [zero_smul, one_smul, mul_zero] at h
    simp [hJ,h]
  let v₀ := ‖v‖⁻¹ • v
  let J₀ := ‖J‖⁻¹ • J
  have hvm : v₀ ∈ S := by
    rw [mem_sphere_zero_iff_norm,norm_smul,norm_inv,norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hJm : J₀ ∈ S := by
    rw [mem_sphere_zero_iff_norm,norm_smul,norm_inv,norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hJ)]
  have hvr : ‖v‖ • v₀ = v := by simp [v₀,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hJr : ‖J‖ • J₀ = J := by simp [J₀,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hJ)]
  have hE := jacobiCurvatureTerm_smul (γ p.1) p.2 v₀ J₀ ‖v‖ ‖J‖
  rw [hvr,hJr] at hE
  have hn : ‖v‖^2*‖J‖ ≥ 0 := mul_nonneg (sq_nonneg _) (norm_nonneg _)
  rw [hE,norm_smul,Real.norm_of_nonneg hn]
  have hb := (hB (p,v₀,J₀) ⟨hp,hvm,hJm⟩).trans (le_max_left B 0)
  exact (mul_le_mul_of_nonneg_left hb hn).trans_eq (by ring)

end CalderonN
