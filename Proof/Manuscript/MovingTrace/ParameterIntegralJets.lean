module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonPaper

variable {P F A : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace A] {μ : Measure A}

/-- Differentiate the Fourier reconstruction and the smooth Taylor
integrals under a uniform, integrable bound for each parameter jet. -/
theorem parameterIntegral_iteratedFDeriv
    {O : Set P} (hO : IsOpen O) (f : P → A → F) (hF : ∀ a, ContDiffOn ℝ ∞ (fun p => f p a) O)
    (hMeas : ∀ p ∈ O, ∀ k : ℕ,
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ k (fun p => f p a) p) μ)
    (B : ℕ → A → ℝ) (hB : ∀ k, Integrable (B k) μ)
    (hBound : ∀ p ∈ O, ∀ a k, ‖iteratedFDeriv ℝ k (fun p => f p a) p‖ ≤ B k a) :
    ContDiffOn ℝ ∞ (fun p => ∫ a, f p a ∂μ) O ∧
    ∀ p ∈ O, ∀ k : ℕ,
      iteratedFDeriv ℝ k (fun p => ∫ a, f p a ∂μ) p =
        ∫ a, iteratedFDeriv ℝ k (fun p => f p a) p ∂μ := by
  let D (k : ℕ) (p : P) (a : A) := iteratedFDeriv ℝ k (fun p => f p a) p
  let J (k : ℕ) (p : P) := ∫ a, D k p a ∂μ
  let L (k : ℕ) := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => P) F
  have hD (k : ℕ) (p : P) (a : A) : fderiv ℝ (fun p => D k p a) p = L k (D (k+1) p a) := by
    simp only [D,iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,L,
      LinearIsometryEquiv.apply_symm_apply]
  have hInt (k : ℕ) (p : P) (hp : p ∈ O) : Integrable (D k p) μ :=
    (hB k).mono' (hMeas p hp k) (Eventually.of_forall (fun a => hBound p hp a k))
  have hDrep (k : ℕ) (p : P) : (fun a => fderiv ℝ (fun p => D k p a) p) =
      (L k).toContinuousLinearEquiv ∘ D (k+1) p := funext (hD k p)
  have hJ' (k : ℕ) (p : P) (hp : p ∈ O) :
      HasFDerivAt (J k) (L k (J (k+1) p)) p := by
    have hpO : O ∈ 𝓝 p := hO.mem_nhds hp
    have hT : HasFDerivAt (J k) (∫ a, fderiv ℝ (fun p => D k p a) p ∂μ) p := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ)
        (F := D k) (F' := fun q a => fderiv ℝ (fun p => D k p a) q)
        (s := O) (bound := B (k+1)) hpO
        (Filter.mem_of_superset hpO (fun q hq => hMeas q hq k)) (hInt k p hp) ?_ ?_ (hB (k+1)) ?_
      · rw [hDrep]
        exact (L k).continuous.comp_aestronglyMeasurable (hMeas p hp (k+1))
      · exact Eventually.of_forall (fun a q hq => by
          change ‖fderiv ℝ (iteratedFDeriv ℝ k (fun p => f p a)) q‖ ≤ _
          rw [norm_fderiv_iteratedFDeriv]
          exact hBound q hq a (k+1))
      · refine Eventually.of_forall (fun a q hq => ?_)
        exact (((hF a).contDiffAt (hO.mem_nhds hq)).differentiableAt_iteratedFDeriv (m := k)
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))).hasFDerivAt
    rw [hDrep] at hT
    have hI : (∫ a, (L k).toContinuousLinearEquiv (D (k+1) p a) ∂μ) = L k (J (k+1) p) := by
      let Lk : (P [×(k+1)]→L[ℝ] F) →L[ℝ] (P →L[ℝ] (P [×k]→L[ℝ] F)) :=
        (L k).toContinuousLinearEquiv.toContinuousLinearMap
      exact ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
        (E := P [×(k+1)]→L[ℝ] F) (Fₗ := P →L[ℝ] (P [×k]→L[ℝ] F)) Lk (hInt (k+1) p hp)
    exact hI ▸ hT
  have hEq (k : ℕ) : EqOn (iteratedFDeriv ℝ k (fun p => ∫ a, f p a ∂μ)) (J k) O := by
    induction k with
    | zero =>
      intro p hp
      let L₀ := (continuousMultilinearCurryFin0 ℝ P F).symm.toContinuousLinearEquiv
      change L₀ (∫ a, f p a ∂μ) = _
      rw [← L₀.integral_comp_comm]
      rfl
    | succ k ih =>
      intro p hp
      have hEq' : (iteratedFDeriv ℝ k (fun p => ∫ a, f p a ∂μ)) =ᶠ[𝓝 p] J k :=
        Filter.mem_of_superset (hO.mem_nhds hp) ih
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,hEq'.fderiv_eq,(hJ' k p hp).fderiv]
      exact (L k).symm_apply_apply _
  refine ⟨?_,fun p hp k => hEq k hp⟩
  apply contDiffOn_of_differentiableOn
  intro k hk p hp
  have hB' : DifferentiableWithinAt ℝ (J k) O p := (hJ' k p hp).differentiableAt.differentiableWithinAt
  refine hB'.congr ?_ ?_
  · intro q hq
    exact (iteratedFDerivWithin_of_isOpen k hO hq).trans (hEq k hq)
  · exact (iteratedFDerivWithin_of_isOpen k hO hp).trans (hEq k hp)

end CalderonPaper
