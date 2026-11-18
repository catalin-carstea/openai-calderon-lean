/- The determinant and volume differentiation proofs from the selected ZIP's
   Calderon/MetricVolumeDifferential.lean, on the present coordinate metric type. -/
import Proof.Normalization
import Proof.Archive.DetIdentity
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
open scoped Matrix.Norms.Operator ContDiff
namespace ShrinkingSpheres

def metricDensity (g : MetricField) (x : X) : ℝ := Real.sqrt (g x).det

def determinantDerivative (M : Mat) : Mat →L[ℝ] ℝ :=
  M.det • ((Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap.comp
    (LinearMap.mulLeft ℝ (M⁻¹)).toContinuousLinearMap)

lemma determinantDerivative_apply (M H : Mat) :
    determinantDerivative M H = M.det * Matrix.trace (M⁻¹ * H) := rfl

lemma hasFDerivAt_det_of_isUnit (M : Mat) (hM : IsUnit M.det) :
    HasFDerivAt (Matrix.det : Mat → ℝ) (determinantDerivative M) M := by
  let L : Mat →L[ℝ] Mat := (LinearMap.mulLeft ℝ (M⁻¹)).toContinuousLinearMap
  have hL : L M = 1 := Matrix.nonsing_inv_mul M hM
  have hI : HasFDerivAt (Matrix.det : Mat → ℝ)
      (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap (L M) := by
    rw [hL]
    exact Matrix.hasFDerivAt_det_one
  have h := (hI.comp M L.hasFDerivAt).const_mul M.det
  have hprod : M.det * (M⁻¹).det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv M hM, Matrix.det_one]
  have he : (fun Y : Mat => M.det * Matrix.det (L Y)) = Matrix.det := by
    funext Y
    change M.det * Matrix.det (M⁻¹ * Y) = Matrix.det Y
    rw [Matrix.det_mul, ← mul_assoc, hprod, one_mul]
  change HasFDerivAt (fun Y : Mat => M.det * Matrix.det (L Y))
    (determinantDerivative M) M at h
  rwa [he] at h

def matrixFieldDerivative (g : MetricField) (x : X) : X →L[ℝ] Mat :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (fderiv ℝ (fun y => g y i j) x).smulRight (Matrix.single i j (1 : ℝ))

lemma matrixFieldDerivative_apply_entry (g : MetricField) (x V : X) (i j : Fin 3) :
    matrixFieldDerivative g x V i j = fderiv ℝ (fun y => g y i j) x V := by
  classical
  have h := Matrix.sum_sum_single (fun a b : Fin 3 =>
    fderiv ℝ (fun y => g y a b) x V)
  simpa [matrixFieldDerivative] using congrArg (fun H : Mat => H i j) h

lemma hasFDerivAt_matrixField_of_entries (g : MetricField) (x : X)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) :
    HasFDerivAt g (matrixFieldDerivative g x) x := by
  classical
  have h : HasFDerivAt
      (fun y => ∑ i : Fin 3, ∑ j : Fin 3, g y i j • Matrix.single i j (1 : ℝ))
      (matrixFieldDerivative g x) x :=
    HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ =>
      (hg i j).hasFDerivAt.smul_const (Matrix.single i j (1 : ℝ))
  have he : (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
      g y i j • Matrix.single i j (1 : ℝ)) = g := by
    funext y
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, Matrix.single i j (g y i j) := by simp
      _ = Matrix.of (g y) := Matrix.sum_sum_single (g y)
      _ = g y := by ext i j; rfl
  rwa [he] at h

lemma hasFDerivAt_metric_determinant (g : MetricField) (x : X)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    HasFDerivAt (fun y => (g y).det)
      ((determinantDerivative (g x)).comp (matrixFieldDerivative g x)) x :=
  (hasFDerivAt_det_of_isUnit (g x) (isUnit_iff_ne_zero.mpr hp.det_pos.ne')).comp x
    (hasFDerivAt_matrixField_of_entries g x hg)

lemma fderiv_metricDensity_apply (g : MetricField) (x V : X)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    fderiv ℝ (metricDensity g) x V = (metricDensity g x / 2) *
      Matrix.trace ((g x)⁻¹ * matrixFieldDerivative g x V) := by
  have hd := hasFDerivAt_metric_determinant g x hg hp
  have hs := hd.sqrt hp.det_pos.ne'
  change HasFDerivAt (metricDensity g) ((1 / (2 * metricDensity g x)) •
    (determinantDerivative (g x)).comp (matrixFieldDerivative g x)) x at hs
  have hsq : (metricDensity g x) ^ 2 = (g x).det := Real.sq_sqrt hp.det_pos.le
  have hv : metricDensity g x ≠ 0 := (Real.sqrt_pos.2 hp.det_pos).ne'
  rw [hs.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, determinantDerivative_apply]
  change (1 / (2 * metricDensity g x)) * ((g x).det * _) = _
  rw [← hsq]
  field_simp [hv]

lemma fderiv_metricDensity_apply_entries (g : MetricField) (x V : X)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    fderiv ℝ (metricDensity g) x V = (metricDensity g x / 2) *
      ∑ i : Fin 3, ∑ j : Fin 3,
        (g x)⁻¹ j i * fderiv ℝ (fun y => g y i j) x V := by
  rw [fderiv_metricDensity_apply g x V hg hp]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixFieldDerivative_apply_entry]
  exact Finset.sum_comm

lemma Elliptic.contDiffOn_density {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) : ContDiffOn ℝ ∞ (metricDensity g) Ω := by
  have hd : ContDiffOn ℝ ∞ (fun x => (g x).det) Ω := by
    classical
    simp_rw [Matrix.det_apply']
    exact ContDiffOn.sum (fun σ _ => contDiffOn_const.mul
      (contDiffOn_prod (fun i _ => h.1 (σ i) i)))
  exact hd.sqrt (fun x hx => (h.posDef hK hx).det_pos.ne')

lemma metricDensity_pos {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) : 0 < metricDensity g y :=
  Real.sqrt_pos.mpr (h.posDef hK hy).det_pos

end ShrinkingSpheres
