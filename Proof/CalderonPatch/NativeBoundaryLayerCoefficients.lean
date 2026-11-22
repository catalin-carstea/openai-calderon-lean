module

public import Proof.CalderonPatch.BoundaryLayerProfiles
public import Proof.CalderonPatch.BoundaryLayerTaylor
public import Proof.CalderonPatch.BoundaryNormalLaplacian

import Proof.CalderonN.CovariantHessian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

public section

noncomputable section
open Filter Set
open scoped ContDiff Matrix.Norms.Elementwise Topology

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I axis coordDeriv MetricField contDiffOn_metric_inv_entry contDiffOn_christoffel)

variable {n : ℕ}

/-- Signed normal coordinates, with height in the zeroth ambient
coordinate and tangential coordinates in the following slots. -/
@[expose] def signedLayerCoordinates : (X n × ℝ) ≃L[ℝ] X (n + 1) :=
  (show (X n × ℝ) ≃ₗ[ℝ] X (n + 1) from
    { toFun := fun x => WithLp.toLp 2 (Fin.cons x.2 (fun j => x.1 j))
      invFun := fun z => (WithLp.toLp 2 (fun j => z j.succ), z 0)
      left_inv := fun _ => rfl
      right_inv := fun z => by
        ext j
        exact Fin.cases rfl (fun _ => rfl) j
      map_add' := fun x y => by
        ext j
        exact Fin.cases rfl (fun _ => rfl) j
      map_smul' := fun a x => by
        ext j
        exact Fin.cases rfl (fun _ => rfl) j }).toContinuousLinearEquiv

@[simp] theorem signedLayerCoordinates_height (x : X n × ℝ) :
    signedLayerCoordinates x 0 = x.2 := rfl

@[simp] theorem signedLayerCoordinates_tangent (x : X n × ℝ) (j : I n) :
    signedLayerCoordinates x j.succ = x.1 j := rfl

theorem signedLayerCoordinates_axis_normal :
    signedLayerCoordinates ((0 : X n), (1 : ℝ)) = axis (0 : I (n + 1)) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [axis, EuclideanSpace.single_apply]
  · simp [axis, EuclideanSpace.single_apply]

theorem signedLayerCoordinates_axis_tangent (j : I n) :
    signedLayerCoordinates (axis j, (0 : ℝ)) = axis j.succ := by
  ext k
  refine Fin.cases ?_ (fun l => ?_) k
  · simp [axis, EuclideanSpace.single_apply]
  · simp [axis, EuclideanSpace.single_apply]

/-- The smooth signed coefficient of an ordinary first derivative in
the native coordinate Laplacian. -/
theorem contDiffOn_laplaceFirstCoeff {O : Set (X (n + 1))} (hO : IsOpen O)
    {g : MetricField (n + 1)} (hg : CalderonN.SmoothMetric O g) (k : I (n + 1)) :
    ContDiffOn ℝ ∞ (fun z => laplaceFirstCoeff g z k) O := by
  unfold laplaceFirstCoeff
  exact (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    (contDiffOn_metric_inv_entry hg i j).mul (contDiffOn_christoffel hO hg k i j)).neg

/-- A scalar Taylor coefficient of a signed coordinate field, restricted
to the boundary and normalized by its factorial. -/
@[expose] def normalFaceTaylor (f : X (n + 1) → ℝ) (k : ℕ) (y : X n) : ℂ :=
  ((iteratedDeriv k (fun t : ℝ => f (signedLayerCoordinates (y,t))) 0 : ℝ) : ℂ) / (k.factorial : ℂ)

@[simp] theorem normalFaceTaylor_zero (f : X (n + 1) → ℝ) (y : X n) :
    normalFaceTaylor f 0 y = (f (signedLayerCoordinates (y,0)) : ℂ) := by
  simp [normalFaceTaylor]

theorem contDiffOn_normalFaceTaylor {O : Set (X (n + 1))} (hO : IsOpen O)
    {f : X (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f O) {U : Set (X n)}
    (hU : MapsTo (fun y : X n => signedLayerCoordinates (y,(0 : ℝ))) U O) (k : ℕ) :
    ContDiffOn ℝ ∞ (normalFaceTaylor f k) U := by
  have hf' := hf.comp (signedLayerCoordinates (n := n)).contDiff.contDiffOn
    (mapsTo_preimage signedLayerCoordinates O)
  have h := contDiffOn_normalTaylorCoeff (hO.preimage signedLayerCoordinates.continuous) hf' hU k
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn h).div_const _

theorem normalFaceTaylor_congr {O : Set (X (n + 1))} (hO : IsOpen O)
    {f g : X (n + 1) → ℝ} (h : EqOn f g O) {y : X n}
    (hy : signedLayerCoordinates (y,(0 : ℝ)) ∈ O) (k : ℕ) :
    normalFaceTaylor f k y = normalFaceTaylor g k y := by
  have hc : Continuous (fun t : ℝ => signedLayerCoordinates (y,t)) :=
    signedLayerCoordinates.continuous.comp (continuous_const.prodMk continuous_id)
  have he : (fun t : ℝ => f (signedLayerCoordinates (y,t))) =ᶠ[𝓝 0]
      (fun t : ℝ => g (signedLayerCoordinates (y,t))) :=
    (h.eventuallyEq_of_mem (hO.mem_nhds hy)).comp_tendsto hc.continuousAt
  rw [normalFaceTaylor, normalFaceTaylor, he.iteratedDeriv_eq k]

/-- The leading tangential quadratic form of the inverse metric on
the actual native face. -/
@[expose] def faceInverseQuadratic (g : MetricField (n + 1)) (ξ : I n → ℝ) (y : X n) : ℝ :=
  ∑ i : I n, ∑ j : I n, ((g (signedLayerCoordinates (y,(0 : ℝ))))⁻¹) i.succ j.succ * ξ i * ξ j

theorem faceInverseQuadratic_pos {O : Set (X (n + 1))}
    {g : MetricField (n + 1)} (hg : CalderonN.SmoothMetric O g) (ξ : I n → ℝ) (hξ : ξ ≠ 0)
    {y : X n} (hy : signedLayerCoordinates (y,(0 : ℝ)) ∈ O) :
    0 < faceInverseQuadratic g ξ y := by
  let ξ₁ : I (n + 1) → ℝ := Fin.cons 0 ξ
  have hξ₁ : ξ₁ ≠ 0 := by
    intro h
    apply hξ
    funext j
    exact congrFun h j.succ
  have hp := (hg.2 _ hy).inv.dotProduct_mulVec_pos hξ₁
  simp only [dotProduct, Matrix.mulVec] at hp
  rw [Fin.sum_univ_succ] at hp
  simp only [ξ₁, Fin.cons_zero, Fin.cons_succ, star_trivial, zero_mul, zero_add] at hp
  unfold faceInverseQuadratic
  refine hp.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ, Fin.cons_zero, mul_zero, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.cons_succ]
  ring

/-- The finite-layer construction takes its coefficients from the
smooth signed inverse metric and the actual Laplacian drifts. -/
@[expose] def boundaryLayerCoefficientsOfMetric {O : Set (X (n + 1))} (hO : IsOpen O)
    (g : MetricField (n + 1)) (hg : CalderonN.SmoothMetric O g) {U : Set (X n)}
    (hU : MapsTo (fun y : X n => signedLayerCoordinates (y,(0 : ℝ))) U O)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0) : BoundaryLayerCoefficients ξ U where
  kappa := fun y => Real.sqrt (faceInverseQuadratic g ξ y)
  inverse l i j := normalFaceTaylor (fun z => (g z)⁻¹ i.succ j.succ) l
  normalDrift l := normalFaceTaylor (fun z => (-2) * laplaceFirstCoeff g z 0) l
  tangentDrift l i := normalFaceTaylor (fun z => laplaceFirstCoeff g z i.succ) l
  kappa_smooth := by
    apply ContDiffOn.sqrt _ (fun _ hy => (faceInverseQuadratic_pos hg ξ hξ (hU hy)).ne')
    unfold faceInverseQuadratic
    have hC : ContDiff ℝ ∞ (fun y : X n => signedLayerCoordinates (y,(0 : ℝ))) :=
      signedLayerCoordinates.contDiff.comp (contDiff_id.prodMk contDiff_const)
    exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      (((contDiffOn_metric_inv_entry hg i.succ j.succ).comp hC.contDiffOn hU).mul
        contDiffOn_const).mul contDiffOn_const
  kappa_pos _ hy := Real.sqrt_pos.2 (faceInverseQuadratic_pos hg ξ hξ (hU hy))
  inverse_smooth l i j := contDiffOn_normalFaceTaylor hO (contDiffOn_metric_inv_entry hg _ _) hU l
  inverse_symm l i j y hy := normalFaceTaylor_congr hO
    (fun z hz => congrFun (congrFun (hg.2 z hz).inv.isHermitian.isSymm j.succ) i.succ)
    (hU hy) l
  normalDrift_smooth l :=
    contDiffOn_normalFaceTaylor hO (contDiffOn_const.mul (contDiffOn_laplaceFirstCoeff hO hg 0)) hU l
  tangentDrift_smooth l i := contDiffOn_normalFaceTaylor hO (contDiffOn_laplaceFirstCoeff hO hg _) hU l
  principal_squared y hy := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (faceInverseQuadratic_pos hg ξ hξ (hU hy)).le]
    simp only [faceInverseQuadratic, Complex.ofReal_sum, Complex.ofReal_mul, normalFaceTaylor_zero]

end CalderonPatch.BoundaryLayer
