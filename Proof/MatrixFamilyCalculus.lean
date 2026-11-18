/- Parameter-generic extension of the supplied MetricVolumeDifferential determinant
   and matrix-field calculus, together with the active inverse identity calculus. -/
import Proof.MetricDensity
import Proof.MetricSmooth
import Proof.InverseMetricDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Operator
namespace ShrinkingSpheres
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def matrixFamilyDensity (G : P → Mat) (p : P) : ℝ := Real.sqrt (G p).det

def matrixFamilyCoefficient (G : P → Mat) (p : P) (i j : I) : ℝ :=
  matrixFamilyDensity G p*(G p)⁻¹ i j

def matrixFamilyDerivative (G : P → Mat) (p : P) : P →L[ℝ] Mat :=
  ∑ i : I,∑ j : I,(fderiv ℝ (fun q => G q i j) p).smulRight (Matrix.single i j (1:ℝ))

lemma matrixFamilyDerivative_apply_entry (G : P → Mat) (p a : P) (i j : I) :
    matrixFamilyDerivative G p a i j = fderiv ℝ (fun q => G q i j) p a := by
  classical
  have h := Matrix.sum_sum_single (fun i j : I => fderiv ℝ (fun q => G q i j) p a)
  simpa [matrixFamilyDerivative] using congrArg (fun H : Mat => H i j) h

lemma hasFDerivAt_matrixFamily_of_entries (G : P → Mat) (p : P)
    (hG : ∀ i j,DifferentiableAt ℝ (fun q => G q i j) p) :
    HasFDerivAt G (matrixFamilyDerivative G p) p := by
  classical
  have h : HasFDerivAt (fun q => ∑ i : I,∑ j : I,G q i j • Matrix.single i j (1:ℝ))
      (matrixFamilyDerivative G p) p :=
    HasFDerivAt.fun_sum (fun i _ => HasFDerivAt.fun_sum (fun j _ =>
      (hG i j).hasFDerivAt.smul_const (Matrix.single i j (1:ℝ))))
  have hFun : (fun q => ∑ i : I,∑ j : I,G q i j • Matrix.single i j (1:ℝ)) = G := by
    funext q
    calc
      _ = ∑ i : I,∑ j : I,Matrix.single i j (G q i j) := by simp
      _ = Matrix.of (G q) := Matrix.sum_sum_single (G q)
      _ = G q := by ext i j;rfl
  rwa [hFun] at h

lemma contDiffOn_matrixFamily_det {S : Set P} (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) :
    ContDiffOn ℝ ∞ (fun q => (G q).det) S := by
  classical
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum (fun σ _ => contDiffOn_const.mul (contDiffOn_prod (fun i _ => hG (σ i) i)))

lemma contDiffOn_matrixFamily_adjugate_entry {S : Set P} (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (i j : I) :
    ContDiffOn ℝ ∞ (fun q => (G q).adjugate i j) S := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply contDiffOn_matrixFamily_det (fun q => (G q).updateRow j (Pi.single i 1))
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simpa [Matrix.updateRow_apply,ha] using hG a b

lemma contDiffOn_matrixFamily_inverse_entry {S : Set P} (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,(G q).det ≠ 0) (i j : I) :
    ContDiffOn ℝ ∞ (fun q => (G q)⁻¹ i j) S := by
  have hD := (contDiffOn_matrixFamily_det G hG).inv hDet
  simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
  exact hD.mul (contDiffOn_matrixFamily_adjugate_entry G hG i j)

lemma contDiffOn_matrixFamily_density {S : Set P} (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,(G q).det ≠ 0) :
    ContDiffOn ℝ ∞ (matrixFamilyDensity G) S := (contDiffOn_matrixFamily_det G hG).sqrt hDet

/-- Jacobi's determinant formula supplies the true density derivative in any
    finite or infinite dimensional real parameter space. -/
lemma fderiv_matrixFamily_density_entries (G : P → Mat) (p a : P)
    (hG : ∀ i j,DifferentiableAt ℝ (fun q => G q i j) p) (hDet : 0 < (G p).det) :
    fderiv ℝ (matrixFamilyDensity G) p a = matrixFamilyDensity G p/2*
      ∑ i : I,∑ j : I,(G p)⁻¹ j i*fderiv ℝ (fun q => G q i j) p a := by
  have hd := (hasFDerivAt_det_of_isUnit (G p) (isUnit_iff_ne_zero.mpr hDet.ne')).comp p
    (hasFDerivAt_matrixFamily_of_entries G p hG)
  have hs := hd.sqrt hDet.ne'
  change HasFDerivAt (matrixFamilyDensity G) ((1/(2*matrixFamilyDensity G p)) •
    (determinantDerivative (G p)).comp (matrixFamilyDerivative G p)) p at hs
  have hSq : (matrixFamilyDensity G p)^2 = (G p).det := Real.sq_sqrt hDet.le
  have hMu : matrixFamilyDensity G p ≠ 0 := (Real.sqrt_pos.mpr hDet).ne'
  rw [hs.fderiv]
  simp only [_root_.smul_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,determinantDerivative_apply]
  have hTrace : Matrix.trace ((G p)⁻¹*matrixFamilyDerivative G p a) =
      ∑ i : I,∑ j : I,(G p)⁻¹ j i*fderiv ℝ (fun q => G q i j) p a := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,matrixFamilyDerivative_apply_entry]
    exact Finset.sum_comm
  rw [hTrace,← hSq]
  field_simp [hMu]

/-- The same true inverse identity gives parameter-generic inverse-entry
    derivatives; no coordinate connection or extra analytic premise is used. -/
lemma fderiv_matrixFamily_inverse_entries {S : Set P} (hS : IsOpen S) (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,(G q).det ≠ 0)
    {p : P} (hp : p ∈ S) (a : P) (i j : I) :
    fderiv ℝ (fun q => (G q)⁻¹ i j) p a =
      -(∑ k : I,∑ l : I,(G p)⁻¹ i k*fderiv ℝ (fun q => G q k l) p a*(G p)⁻¹ l j) := by
  let D : Mat := fun k l => fderiv ℝ (fun q => G q k l) p a
  let H : Mat := fun k l => fderiv ℝ (fun q => (G q)⁻¹ k l) p a
  have hF (k l : I) := ((hG k l).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp) |>.hasFDerivAt
  have hI (k l : I) := ((contDiffOn_matrixFamily_inverse_entry G hG hDet k l).contDiffAt
    (hS.mem_nhds hp)).differentiableAt (by simp) |>.hasFDerivAt
  have hMat : H*G p+(G p)⁻¹*D = 0 := by
    ext k l
    have hConst : (fun q => ∑ t : I,(G q)⁻¹ k t*G q t l) =ᶠ[𝓝 p]
        (fun _ => if k=l then (1:ℝ) else 0) := by
      filter_upwards [hS.mem_nhds hp] with q hq
      simpa only [Matrix.mul_apply,Matrix.one_apply] using congrArg (fun T : Mat => T k l)
        (Matrix.nonsing_inv_mul (G q) (isUnit_iff_ne_zero.mpr (hDet q hq)))
    have hZero := congrArg (fun T : P →L[ℝ] ℝ => T a) hConst.fderiv_eq
    have hSum := HasFDerivAt.sum (u:=Finset.univ) (fun t _ => (hI k t).mul (hF t l))
    have hFun : (fun q => ∑ t : I,(G q)⁻¹ k t*G q t l) =
        ∑ t : I,(fun q => (G q)⁻¹ k t)*(fun q => G q t l) := by funext q;rfl
    rw [hFun,hSum.fderiv] at hZero
    simp only [_root_.sum_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,fderiv_const_apply,zero_apply] at hZero
    change (∑ t : I,fderiv ℝ (fun q => (G q)⁻¹ k t) p a*G p t l)+
      (∑ t : I,(G p)⁻¹ k t*fderiv ℝ (fun q => G q t l) p a) = 0
    simpa only [Finset.sum_add_distrib,mul_comm,add_comm] using hZero
  have hMul := congrArg (fun T : Mat => T*(G p)⁻¹) hMat
  rw [Matrix.add_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv (G p)
    (isUnit_iff_ne_zero.mpr (hDet p hp)),Matrix.mul_one,Matrix.zero_mul] at hMul
  have hEntry := congrArg (fun T : Mat => T i j) hMul
  simp only [Matrix.add_apply,Matrix.zero_apply] at hEntry
  change H i j = _
  have hEq : H i j = -(((G p)⁻¹*D*(G p)⁻¹) i j) := by linarith only [hEntry]
  rw [hEq]
  congr 1
  change (∑ l : I,(∑ k : I,(G p)⁻¹ i k*fderiv ℝ (fun q => G q k l) p a)*(G p)⁻¹ l j) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

end ShrinkingSpheres
