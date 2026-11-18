import Proof.Archive.CoordinateRotationCoefficientFamily
import Proof.ConnectionOperatorBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.ConnectionError OAI.AnisotropicCalderon.MetricOperator
open OAI.AnisotropicCalderon.MetricVolume
open OAI.AnisotropicCalderon.SmoothSphereRotation

def rotationVectorL (i j : I) : X →L[ℝ] X :=
  (EuclideanSpace.proj i).smulRight (axis j)-(EuclideanSpace.proj j).smulRight (axis i)

lemma rotationVectorL_apply (i j : I) (z : X) : rotationVectorL i j z = rotationVector i j z := rfl

lemma norm_rotationVectorL_le_two (i j : I) : ‖rotationVectorL i j‖ ≤ 2 := by
  have h (k l : I) : ‖(EuclideanSpace.proj k : X →L[ℝ] ℝ).smulRight (axis l)‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply,norm_axis,mul_one]
    exact norm_euclidean_proj_le_one k
  exact (norm_sub_le _ _).trans (by linarith only [h i j,h j i])

lemma norm_rotationVector_le_two (i j : I) (z : X) : ‖rotationVector i j z‖ ≤ 2*‖z‖ :=
  ((rotationVectorL i j).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (norm_rotationVectorL_le_two i j) (norm_nonneg z))

def coordinateRotationGeneratorMatrix (i j : I) : Mat := operatorMatrixMap (rotationVectorL i j)

lemma coordinateRotationGeneratorMatrix_entry (i j k l : I) :
    coordinateRotationGeneratorMatrix i j k l = rotationVector i j (axis l) k := by
  have h := matrixOperator_basis_inner (coordinateRotationGeneratorMatrix i j) k l
  change inner ℝ ((operatorMatrixMap _).toEuclideanLin (axis l)) (axis k) = _ at h
  rw [operatorMatrixMap_apply] at h
  simpa only [rotationVectorL_apply,axis,EuclideanSpace.inner_single_right,one_mul,conj_trivial] using h.symm

lemma coordinateRotationGeneratorMatrix_entry_bound (i j k l : I) :
    |coordinateRotationGeneratorMatrix i j k l| ≤ 2 := by
  rw [coordinateRotationGeneratorMatrix_entry]
  exact (PiLp.norm_apply_le (rotationVector i j (axis l)) k).trans
    ((norm_rotationVector_le_two i j (axis l)).trans_eq (by rw [norm_axis,mul_one]))

theorem hasDerivAt_coordinateRotationMatrix_zero (i j : I) :
    HasDerivAt (coordinateRotationMatrix i j) (coordinateRotationGeneratorMatrix i j) 0 := by
  apply hasDerivAt_pi.mpr
  intro k
  apply hasDerivAt_pi.mpr
  intro l
  have hR := hasDerivAt_coordinateRotation i j 0 (axis l)
  rw [coordinateRotation_zero] at hR
  have h := (EuclideanSpace.proj k : X →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hR
  simpa only [coordinateRotationMatrix_entry,coordinateVector,axis,coordinateRotationGeneratorMatrix_entry,
    PiLp.proj_apply,Function.comp_def] using h

lemma hasDerivAt_matrix_mul {A B : ℝ → Mat} {DA DB : Mat} {t : ℝ}
    (hA : HasDerivAt A DA t) (hB : HasDerivAt B DB t) :
    HasDerivAt (fun s => A s*B s) (DA*B t+A t*DB) t := by
  apply hasDerivAt_pi.mpr
  intro k
  apply hasDerivAt_pi.mpr
  intro l
  have hSum := HasDerivAt.sum (fun q (_ : q ∈ Finset.univ) =>
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hA k) q).mul
        (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB q) l)))
  have hFun : (∑ q : I,(fun x : ℝ => A x k q)*(fun x : ℝ => B x q l)) =
      (fun x : ℝ => ∑ q : I,A x k q*B x q l) := by
    funext x
    simp only [Finset.sum_apply,Pi.mul_apply]
  rw [hFun] at hSum
  simpa only [Matrix.mul_apply,Matrix.add_apply,Finset.sum_add_distrib] using hSum

lemma hasDerivAt_matrix_transpose {A : ℝ → Mat} {DA : Mat} {t : ℝ}
    (hA : HasDerivAt A DA t) : HasDerivAt (fun s => (A s).transpose) DA.transpose t := by
  apply hasDerivAt_pi.mpr
  intro k
  apply hasDerivAt_pi.mpr
  intro l
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA l) k

/-- Actual angular derivative of the orthogonally transformed coefficient:
    the two matrix actions and the spatial rotation field occur together. -/
def rotationPrincipalCoefficientDerivative (i j : I) (a : X → Mat) (z : X) : Mat :=
  (coordinateRotationGeneratorMatrix i j).transpose*a z+
    a z*coordinateRotationGeneratorMatrix i j+fderiv ℝ a z (rotationVector i j z)

theorem hasDerivAt_coordinateRotationPrincipal_zero (i j : I) (a : X → Mat) (z : X)
    (ha : DifferentiableAt ℝ a z) :
    HasDerivAt (fun t : ℝ => coordinateRotationPrincipalFamily i j (fun q : ℝ × X => a q.2) ((t,0),z))
      (rotationPrincipalCoefficientDerivative i j a z) 0 := by
  have hRot := hasDerivAt_coordinateRotation i j 0 z
  rw [coordinateRotation_zero] at hRot
  have ha0 : DifferentiableAt ℝ a (coordinateRotation i j 0 z) := by
    simpa only [coordinateRotation_zero] using ha
  have hA := ha0.hasFDerivAt.comp_hasDerivAt 0 hRot
  have hM := hasDerivAt_coordinateRotationMatrix_zero i j
  have hProd := hasDerivAt_matrix_mul (hasDerivAt_matrix_mul (hasDerivAt_matrix_transpose hM) hA) hM
  simpa only [coordinateRotationMatrix_zero,coordinateRotation_zero,Matrix.transpose_one,
    one_mul,mul_one,rotationPrincipalCoefficientDerivative,coordinateRotationPrincipalFamily,
    Function.comp_def,add_assoc,add_comm,add_left_comm] using hProd

/-- A quantitative first angular coefficient derivative from its value and
    spatial first jet. The bound has no parameter/frame derivative term. -/
theorem rotationPrincipalCoefficientDerivative_entry_bound (i j : I) (a : X → Mat) (z : X)
    (V D : ℝ) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (hValue : ∀ k l,|a z k l| ≤ V) (hDerivative : ‖fderiv ℝ a z‖ ≤ D) (k l : I) :
    |rotationPrincipalCoefficientDerivative i j a z k l| ≤ 12*V+2*D*‖z‖ := by
  let Q := coordinateRotationGeneratorMatrix i j
  have hFirst : |(Q.transpose*a z) k l| ≤ 6*V := by
    calc
      _ = |∑ q : I,Q q k*a z q l| := rfl
      _ ≤ ∑ q : I,|Q q k*a z q l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q : I,2*V := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul]
        exact mul_le_mul (coordinateRotationGeneratorMatrix_entry_bound i j q k) (hValue q l)
          (abs_nonneg _) (by norm_num)
      _ = 6*V := by simp;ring
  have hSecond : |(a z*Q) k l| ≤ 6*V := by
    calc
      _ = |∑ q : I,a z k q*Q q l| := rfl
      _ ≤ ∑ q : I,|a z k q*Q q l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q : I,V*2 := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul]
        exact mul_le_mul (hValue k q) (coordinateRotationGeneratorMatrix_entry_bound i j q l)
          (abs_nonneg _) hV
      _ = 6*V := by simp;ring
  have hLast : |fderiv ℝ a z (rotationVector i j z) k l| ≤ D*(2*‖z‖) := by
    have hEntry := Matrix.norm_entry_le_entrywise_sup_norm (fderiv ℝ a z (rotationVector i j z)) (i:=k) (j:=l)
    have hFull := ((fderiv ℝ a z).le_opNorm (rotationVector i j z)).trans
      (mul_le_mul hDerivative (norm_rotationVector_le_two i j z) (norm_nonneg _) hD)
    exact hEntry.trans hFull
  change |((Q.transpose*a z) k l+(a z*Q) k l)+fderiv ℝ a z (rotationVector i j z) k l| ≤ _
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hFirst hSecond) hLast).trans_eq (by ring))

lemma norm_matrix_mul_left_entry_bound (Q A : Mat) (C : ℝ) (hC : 0 ≤ C)
    (hQ : ∀ k l,|Q k l| ≤ C) : ‖Q*A‖ ≤ 3*C*‖A‖ := by
  apply (Matrix.norm_le_iff (by positivity : 0 ≤ 3*C*‖A‖)).mpr
  intro k l
  change |(Q*A) k l| ≤ _
  calc
    _ = |∑ q : I,Q k q*A q l| := rfl
    _ ≤ ∑ q : I,|Q k q*A q l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : I,C*‖A‖ := by
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul]
      exact mul_le_mul (hQ k q) (Matrix.norm_entry_le_entrywise_sup_norm A (i:=q) (j:=l))
        (abs_nonneg _) hC
    _ = _ := by simp;ring

lemma norm_matrix_mul_right_entry_bound (Q A : Mat) (C : ℝ) (hC : 0 ≤ C)
    (hQ : ∀ k l,|Q k l| ≤ C) : ‖A*Q‖ ≤ 3*C*‖A‖ := by
  apply (Matrix.norm_le_iff (by positivity : 0 ≤ 3*C*‖A‖)).mpr
  intro k l
  change |(A*Q) k l| ≤ _
  calc
    _ = |∑ q : I,A k q*Q q l| := rfl
    _ ≤ ∑ q : I,|A k q*Q q l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : I,‖A‖*C := by
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A (i:=k) (j:=q)) (hQ q l)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp;ring

def generatorLeftMatrixL (i j : I) : Mat →L[ℝ] Mat := by
  let Q := coordinateRotationGeneratorMatrix i j
  let L : Mat →ₗ[ℝ] Mat :=
    { toFun := fun A => Q.transpose*A
      map_add' := fun A B => Matrix.mul_add _ _ _
      map_smul' := fun c A => by simp only [Matrix.mul_smul,RingHom.id_apply] }
  apply L.mkContinuous 6
  intro A
  exact (norm_matrix_mul_left_entry_bound Q.transpose A 2 (by norm_num)
    (fun k l => coordinateRotationGeneratorMatrix_entry_bound i j l k)).trans_eq (by ring)

def generatorRightMatrixL (i j : I) : Mat →L[ℝ] Mat := by
  let Q := coordinateRotationGeneratorMatrix i j
  let L : Mat →ₗ[ℝ] Mat :=
    { toFun := fun A => A*Q
      map_add' := fun A B => Matrix.add_mul _ _ _
      map_smul' := fun c A => by simp only [Matrix.smul_mul,RingHom.id_apply] }
  apply L.mkContinuous 6
  intro A
  exact (norm_matrix_mul_right_entry_bound Q A 2 (by norm_num)
    (coordinateRotationGeneratorMatrix_entry_bound i j)).trans_eq (by ring)

def generatorPairMatrixL (i j : I) : Mat →L[ℝ] Mat := generatorLeftMatrixL i j+generatorRightMatrixL i j

lemma norm_generatorPairMatrixL_le_twelve (i j : I) : ‖generatorPairMatrixL i j‖ ≤ 12 := by
  have hLeft : ‖generatorLeftMatrixL i j‖ ≤ 6 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro A
    exact (norm_matrix_mul_left_entry_bound _ A 2 (by norm_num)
      (fun k l => coordinateRotationGeneratorMatrix_entry_bound i j l k)).trans_eq (by ring)
  have hRight : ‖generatorRightMatrixL i j‖ ≤ 6 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro A
    exact (norm_matrix_mul_right_entry_bound _ A 2 (by norm_num)
      (coordinateRotationGeneratorMatrix_entry_bound i j)).trans_eq (by ring)
  exact (norm_add_le _ _).trans (by linarith only [hLeft,hRight])

/-- The spatial first derivative of the true angular coefficient derivative
    uses only the spatial first and second jets of the original coefficient. -/
theorem norm_fderiv_rotationPrincipalCoefficientDerivative_le (i j : I) (a : X → Mat) (z : X)
    (ha : DifferentiableAt ℝ a z) (hDa : DifferentiableAt ℝ (fderiv ℝ a) z)
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hFirst : ‖fderiv ℝ a z‖ ≤ D) (hSecond : ‖fderiv ℝ (fderiv ℝ a) z‖ ≤ E) :
    ‖fderiv ℝ (rotationPrincipalCoefficientDerivative i j a) z‖ ≤ 14*D+2*E*‖z‖ := by
  let G := generatorPairMatrixL i j
  have hG := G.hasFDerivAt.comp z ha.hasFDerivAt
  have hRot : HasFDerivAt (rotationVector i j) (rotationVectorL i j) z := (rotationVectorL i j).hasFDerivAt
  have hProduct := hDa.hasFDerivAt.clm_apply hRot
  have hDeriv := hG.add hProduct
  simp only [Function.comp_def,Pi.add_apply] at hDeriv
  have hFun : (fun w => G (a w)+fderiv ℝ a w (rotationVector i j w)) =
      rotationPrincipalCoefficientDerivative i j a := by
    funext w
    rfl
  rw [← hFun]
  change ‖fderiv ℝ ((fun w => G (a w))+(fun w => fderiv ℝ a w (rotationVector i j w))) z‖ ≤ _
  rw [hDeriv.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  change ‖G (fderiv ℝ a z b)+(fderiv ℝ a z (rotationVectorL i j b)+
    fderiv ℝ (fderiv ℝ a) z b (rotationVector i j z))‖ ≤ _
  have hOne : ‖G (fderiv ℝ a z b)‖ ≤ 12*D*‖b‖ :=
    (G.le_opNorm _).trans ((mul_le_mul (norm_generatorPairMatrixL_le_twelve i j)
      (((fderiv ℝ a z).le_opNorm b).trans (mul_le_mul_of_nonneg_right hFirst (norm_nonneg b)))
        (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hTwo : ‖fderiv ℝ a z (rotationVectorL i j b)‖ ≤ D*(2*‖b‖) :=
    ((fderiv ℝ a z).le_opNorm _).trans
      (mul_le_mul hFirst (norm_rotationVector_le_two i j b) (norm_nonneg _) hD)
  have hThree : ‖fderiv ℝ (fderiv ℝ a) z b (rotationVector i j z)‖ ≤ E*‖b‖*(2*‖z‖) :=
    (ContinuousLinearMap.le_opNorm₂ _ b _).trans (by gcongr;exact norm_rotationVector_le_two i j z)
  exact ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))).trans
    ((add_le_add hOne (add_le_add hTwo hThree)).trans_eq (by ring))

end ShrinkingSpheres
