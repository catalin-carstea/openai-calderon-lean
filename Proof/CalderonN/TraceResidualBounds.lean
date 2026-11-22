module

public import Proof.CalderonN.TraceCutoffAlgebra
public import Proof.CalderonN.FiberEnergy

import Mathlib.Tactic

/-! Adapted from `TraceResidualBounds` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_real_mul_le {a : ℝ} {u : ℂ} {A U : ℝ}
    (ha : |a| ≤ A) (hu : ‖u‖ ≤ U) :
    ‖(a : ℂ) * u‖ ≤ A*U := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul ha hu (norm_nonneg _) ((abs_nonneg _).trans ha)

theorem norm_coordinate_sum_le {f : I dim → ℂ} {A : ℝ} (h : ∀ i, ‖f i‖ ≤ A) :
    ‖∑ i, f i‖ ≤ (dim : ℝ)*A := by
  exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i))

/-- The exact trace commutator is bounded by one radius-weighted trace
derivative and a radius-weighted zeroth-order term. -/
theorem norm_traceCutoffResidual_le
    (γ g₂ : (MetricField dim)) (r : (X dim) → ℝ) (A : (TraceAdjoint dim)) (χ : (X dim) → ℝ) (u : (Field dim))
    (p : (X dim) × (X dim)) {Q Q₂ G P D U V : ℝ}
    (hQ : ∀ i, |coordDeriv i χ p.1| ≤ Q)
    (hQ₂ : ∀ i j, |coordDeriv i (coordDeriv j χ) p.1| ≤ Q₂)
    (hG : ∀ k i j, |christoffel γ p.1 k i j| ≤ G)
    (hP : ∀ i j, |principal γ g₂ p.1 i j| ≤ P)
    (hD : ∀ k, |drift γ g₂ p.1 k| ≤ D)
    (hu : ‖(r p.1 : ℂ) * u p‖ ≤ U)
    (hW : ∀ i, ‖(r p.1 : ℂ) * traceDerivative γ A i u p‖ ≤ V) :
    ‖traceCutoffResidual γ g₂ r A χ u p‖ ≤
      (dim : ℝ)^2*P*(Q₂*U + 2*Q*V + (dim : ℝ)*G*Q*U) + (dim : ℝ)*D*Q*U := by
  let a (i : (I dim)) := coordDeriv i χ p.1
  let b (i j : (I dim)) := coordDeriv i (coordDeriv j χ) p.1
  let v := (r p.1 : ℂ) * u p
  let w (i : (I dim)) := (r p.1 : ℂ) * traceDerivative γ A i u p
  let L (i j : (I dim)) :=
    (b i j : ℂ) * v + (a i : ℂ) * w j + (a j : ℂ) * w i -
      ∑ k, (christoffel γ p.1 k i j : ℂ) * ((a k : ℂ) * v)
  have he : traceCutoffResidual γ g₂ r A χ u p =
      (∑ i, ∑ j, (principal γ g₂ p.1 i j : ℂ) * L i j) +
        ∑ k, (drift γ g₂ p.1 k : ℂ) * ((a k : ℂ) * v) := by
    simp only [traceCutoffResidual,L,a,b,v,w]
    simp only [mul_add,mul_sub,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    ring_nf
    have hjet : (∑ i, ∑ j, (r p.1 : ℂ) * (principal γ g₂ p.1 i j : ℂ) *
        ((coordDeriv i (coordDeriv j χ) p.1 : ℝ) : ℂ) * u p) =
      ∑ i, ∑ j, (r p.1 : ℂ) * u p * (principal γ g₂ p.1 i j : ℂ) *
        ((coordDeriv i (coordDeriv j χ) p.1 : ℝ) : ℂ) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hjet]
    ring
  have hL (i j : (I dim)) : ‖L i j‖ ≤ Q₂*U + 2*Q*V + (dim : ℝ)*G*Q*U := by
    unfold L
    apply (norm_sub_le _ _).trans
    have h₁ := norm_real_mul_le (hQ₂ i j) hu
    have h₂ := norm_real_mul_le (hQ i) (hW j)
    have h₃ := norm_real_mul_le (hQ j) (hW i)
    have h₄ : ‖∑ k, (christoffel γ p.1 k i j : ℂ) * ((a k : ℂ) * v)‖ ≤ (dim : ℝ)*(G*(Q*U)) :=
      norm_coordinate_sum_le (fun k => norm_real_mul_le (hG k i j) (norm_real_mul_le (hQ k) hu))
    have hadd₁ := norm_add_le ((b i j : ℂ)*v) ((a i : ℂ)*w j)
    have hadd₂ := norm_add_le ((b i j : ℂ)*v + (a i : ℂ)*w j) ((a j : ℂ)*w i)
    linarith only [h₁,h₂,h₃,h₄,hadd₁,hadd₂]
  rw [he]
  apply (norm_add_le _ _).trans
  have h₁ : ‖∑ i, ∑ j, (principal γ g₂ p.1 i j : ℂ) * L i j‖ ≤
      (dim : ℝ)*((dim : ℝ)*(P*(Q₂*U + 2*Q*V + (dim : ℝ)*G*Q*U))) :=
    norm_coordinate_sum_le fun i => norm_coordinate_sum_le fun j => norm_real_mul_le (hP i j) (hL i j)
  have h₂ : ‖∑ k, (drift γ g₂ p.1 k : ℂ) * ((a k : ℂ) * v)‖ ≤ (dim : ℝ)*(D*(Q*U)) :=
    norm_coordinate_sum_le fun k => norm_real_mul_le (hD k) (norm_real_mul_le (hQ k) hu)
  convert add_le_add h₁ h₂ using 1 <;> ring

/-- All commutator coefficients vanish at a point where the differential of
the cutoff vanishes on a neighborhood. -/
theorem traceCutoffResidual_eq_zero_off_differential_support
    (γ g₂ : (MetricField dim)) (r : (X dim) → ℝ) (A : (TraceAdjoint dim)) (χ : (X dim) → ℝ) (u : (Field dim))
    (p : (X dim) × (X dim)) (hp : p.1 ∉ tsupport (fderiv ℝ χ)) :
    traceCutoffResidual γ g₂ r A χ u p = 0 := by
  have he : fderiv ℝ χ =ᶠ[nhds p.1] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
  have h (i : (I dim)) : coordDeriv i χ =ᶠ[nhds p.1] 0 := by
    filter_upwards [he] with y hy
    simp [coordDeriv,hy]
  have h₁ (i : (I dim)) : coordDeriv i χ p.1 = 0 := (h i).eq_of_nhds
  have h₂ (i j : (I dim)) : coordDeriv i (coordDeriv j χ) p.1 = 0 := by
    simp [coordDeriv,(h j).fderiv_eq (𝕜 := ℝ)]
  simp [traceCutoffResidual,h₁,h₂]

/-- Uniform pointwise residual control gives the protected weighted
output norm bound through the exact probability-sphere measure. -/
theorem traceNorm_le_of_pointwise {Y : Set (X dim)} (d : (Data dim)) (φ : (Field dim)) {M : ℝ}
    (hM : 0 ≤ M) (hYm : MeasurableSet Y) (hV : IntegrableOn (chartVolume d.γ) Y)
    (hpt : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
      ‖movingTrace d.γ d.g₂ d.radius d.adjoint φ (y,frameVector d.frame y w)‖ ≤ M) :
    traceNorm Y d φ ≤ M * Real.sqrt (∫ y in Y, chartVolume d.γ y) := by
  let F := movingTrace d.γ d.g₂ d.radius d.adjoint φ
  have hFiber (y : (X dim)) (hy : y ∈ Y) : fiberSq d.frame y (fun w => F (y,w)) ≤ M^2 := by
    rw [fiberSq_eq_integral_norm_sq]
    change (∫ w : ↥(standardSphere dim), ‖F (y,frameVector d.frame y w)‖^2 ∂sphereProbability dim) ≤ M^2
    have h := integral_mono_of_nonneg
      (μ := (sphereProbability dim)) (f := fun w : ↥(standardSphere dim) => ‖F (y,frameVector d.frame y w)‖^2)
      (g := fun _ : ↥(standardSphere dim) => M^2)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (integrable_const _)
      (Filter.Eventually.of_forall fun w => pow_le_pow_left₀ (norm_nonneg _) (hpt y hy w) 2)
    simpa only [integral_const,probReal_univ,one_smul] using h
  have hv (y : (X dim)) : 0 ≤ chartVolume d.γ y := Real.sqrt_nonneg _
  have hY : ∀ᵐ y ∂((volume : Measure (X dim)).restrict Y),
      chartVolume d.γ y * fiberSq d.frame y (fun w => F (y,w)) ≤ M^2 * chartVolume d.γ y := by
    apply ae_restrict_of_forall_mem hYm
    intro y hy
    rw [mul_comm (M^2)]
    exact mul_le_mul_of_nonneg_left (hFiber y hy) (hv y)
  have ht := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => mul_nonneg (hv y) (fiberSq_nonneg _ _ _))
    (hV.const_mul (M^2)) hY
  rw [integral_const_mul] at ht
  change Real.sqrt (∫ y in Y, chartVolume d.γ y * fiberSq d.frame y (fun w => F (y,w))) ≤ _
  refine (Real.sqrt_le_sqrt ht).trans_eq ?_
  rw [Real.sqrt_mul (sq_nonneg M),Real.sqrt_sq hM]

/-- The constant mode and the values on the derivative support suffice
for a bound in the protected trace norm. -/
theorem traceNorm_cutoffDensity_le_of_bounds
    {Y : Set (X dim)} (d : (Data dim)) (hYm : MeasurableSet Y) (hVol : IntegrableOn (chartVolume d.γ) Y)
    (hA : ∀ i y, IsLinearMap ℂ (d.adjoint i y)) {χ : (X dim) → ℝ} {ψ : (Field dim)}
    (hχ : ContDiff ℝ 2 χ) (hψ : Differentiable ℝ ψ)
    (hDψ : ∀ i, Differentiable ℝ (traceDerivative d.γ d.adjoint i ψ))
    (hD₁ : ∀ i, Differentiable ℝ (traceDerivative d.γ d.adjoint i (1 : (Field dim))))
    (hEq : movingTrace d.γ d.g₂ d.radius d.adjoint ψ = 0)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hconst : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
      ‖baseMul χ (movingTrace d.γ d.g₂ d.radius d.adjoint (1 : (Field dim)))
        (y,frameVector d.frame y w)‖ ≤ M₀)
    (hcomm : ∀ y ∈ Y, y ∈ tsupport (fderiv ℝ χ) → ∀ w : ↥(standardSphere dim),
      ‖traceCutoffResidual d.γ d.g₂ d.radius d.adjoint χ (ψ-1)
        (y,frameVector d.frame y w)‖ ≤ M₁) :
    traceNorm Y d (cutoffDensity χ ψ) ≤ (M₀+M₁) * Real.sqrt (∫ y in Y, chartVolume d.γ y) := by
  apply traceNorm_le_of_pointwise d _ (add_nonneg hM₀ hM₁) hYm hVol
  intro y hy w
  rw [movingTrace_cutoffDensity d hA hχ hψ hDψ hD₁ hEq]
  have hR : ‖traceCutoffResidual d.γ d.g₂ d.radius d.adjoint χ (ψ-1)
      (y,frameVector d.frame y w)‖ ≤ M₁ := by
    by_cases h : y ∈ tsupport (fderiv ℝ χ)
    · exact hcomm y hy h w
    · rw [traceCutoffResidual_eq_zero_off_differential_support _ _ _ _ _ _
          (y,frameVector d.frame y w) h,norm_zero]
      exact hM₁
  exact (norm_add_le _ _).trans (add_le_add (by simpa only [Pi.neg_apply,norm_neg] using hconst y hy w) hR)

end CalderonN
