module

public import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricVolumeDifferential
import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-! Adapted from the reviewed Proposition 5.3 release's
`Proof/Archive/CoordinatePiolaCovariance.lean`,
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. -/

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Operator

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def coordinateJacobian (F : (X dim) → (X dim)) (x : (X dim)) : (Mat dim) :=
  coordinateMatrix (fderiv ℝ F x)

theorem coordinateJacobian_det_ne_zero {F : (X dim) → (X dim)} {x : (X dim)}
    (hF : Function.Bijective (fderiv ℝ F x)) : (coordinateJacobian F x).det ≠ 0 := by
  let A := fderiv ℝ F x
  let e := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hF.1) (LinearMap.range_eq_top.mpr hF.2)
  exact coordinateMatrix_det_ne_zero e

@[expose] def coordinateFluxDivergence (Z : (X dim) → (X dim)) (x : (X dim)) : ℝ :=
  ∑ i : (I dim), coordDeriv i (fun y => Z y i) x

theorem coordinateFluxDivergence_congr_germ {A B : (X dim) → (X dim)} {x : (X dim)}
    (h : A =ᶠ[𝓝 x] B) : coordinateFluxDivergence A x = coordinateFluxDivergence B x := by
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y => A y i) =ᶠ[𝓝 x] (fun y => B y i) :=
    h.mono (fun y hy => congrArg (fun z : (X dim) => z i) hy)
  exact congrArg (fun T : (X dim) →L[ℝ] ℝ => T (axis i)) hi.fderiv_eq

@[expose] def signedPiolaFlux (F Z : (X dim) → (X dim)) (x : (X dim)) : (X dim) :=
  WithLp.toLp 2 fun i => ∑ k, (coordinateJacobian F x).adjugate i k * Z (F x) k

theorem contDiff_coordinateJacobian_entry
    (F : (X dim) → (X dim)) (hF : ContDiff ℝ ∞ F) (i j : (I dim)) :
    ContDiff ℝ ∞ (fun y => coordinateJacobian F y i j) :=
  by
    simp only [coordinateJacobian,coordinateMatrix_apply]
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
      ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem fderiv_coordinateJacobian_entry (F : (X dim) → (X dim)) (hF : ContDiff ℝ ∞ F)
    (x V : (X dim)) (i j : (I dim)) :
    fderiv ℝ (fun y => coordinateJacobian F y i j) x V =
      (fderiv ℝ (fderiv ℝ F) x V (axis j)) i := by
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have he := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (axis j) x)
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x he
  simp only [coordinateJacobian,coordinateMatrix_apply]
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘
    (fun y => fderiv ℝ F y (axis j))) x V = _
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rfl

/-- The determinant and inverse derivatives cancel after exchanging the two
    differentiated columns of the Jacobian. -/
theorem coordinateJacobian_adjugate_column_divergence
    (F : X dim → X dim) (hF : ContDiff ℝ ∞ F) (x : X dim)
    (hJ : (coordinateJacobian F x).det ≠ 0) (k : I dim) :
    (∑ i : I dim, fderiv ℝ (fun y => (coordinateJacobian F y).adjugate i k) x
      (axis i)) = 0 := by
  let A := coordinateJacobian F
  let B := (A x)⁻¹
  let D (i a b : I dim) := fderiv ℝ (fun y => A y a b) x (axis i)
  have hs (i a b : I dim) : D i a b = D b a i := by
    dsimp only [D, A]
    rw [fderiv_coordinateJacobian_entry F hF, fderiv_coordinateJacobian_entry F hF]
    rw [(hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq (axis i) (axis b)]
  have hA (a b : I dim) : DifferentiableAt ℝ (fun y => A y a b) x :=
    (contDiff_coordinateJacobian_entry F hF a b).differentiable (by simp) x
  have hDA := hasFDerivAt_matrixField_of_entries A x hA
  have hDet : HasFDerivAt (fun y => (A y).det)
      ((determinantDerivative (A x)).comp (matrixFieldDerivative A x)) x :=
    (hasFDerivAt_det_of_isUnit (A x) (isUnit_iff_ne_zero.mpr hJ)).comp x hDA
  have hInv := (hasFDerivAt_inverseMatrix_of_isUnit (A x)
    ((Matrix.isUnit_iff_isUnit_det (A x)).mpr (isUnit_iff_ne_zero.mpr hJ))).comp x hDA
  have he : ∀ᶠ y in 𝓝 x, (A y).adjugate = (A y).det • (A y)⁻¹ := by
    filter_upwards [hDet.continuousAt.eventually_ne hJ] with y hy
    change (A y).det ≠ 0 at hy
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hy, one_smul]
  have hdet (i : I dim) : fderiv ℝ (fun y => (A y).det) x (axis i) =
      (A x).det * ∑ a, ∑ b, B b a * D i a b := by
    rw [hDet.fderiv]
    simp only [ContinuousLinearMap.comp_apply, determinantDerivative_apply, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, matrixFieldDerivative_apply_entry]
    congr 1
    exact Finset.sum_comm
  have hinv (i j l : I dim) : fderiv ℝ (fun y => (A y)⁻¹ j l) x (axis i) =
      -∑ a, ∑ b, B j a * D i a b * B b l := by
    let E : Mat dim →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ j l).toContinuousLinearMap
    have h := E.hasFDerivAt.comp x hInv
    change HasFDerivAt (fun y => (A y)⁻¹ j l) _ x at h
    rw [h.fderiv]
    change -((A x)⁻¹ * matrixFieldDerivative A x (axis i) * (A x)⁻¹) j l = _
    simp only [Matrix.mul_apply, matrixFieldDerivative_apply_entry, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun b a => B j a * D i a b * B b l)]
  have hentry (i : I dim) : fderiv ℝ (fun y => (A y).adjugate i k) x (axis i) =
      (A x).det * ((∑ a, ∑ b, B b a * D i a b * B i k) -
        ∑ a, ∑ b, B i a * D i a b * B b k) := by
    have he' : (fun y => (A y).adjugate i k) =ᶠ[𝓝 x] (fun y => (A y).det * (A y)⁻¹ i k) :=
      he.mono fun y hy => by
        change (A y).adjugate i k = (A y).det * (A y)⁻¹ i k
        exact congrArg (fun V : Mat dim => V i k) hy
    have hI : DifferentiableAt ℝ (fun y => (A y)⁻¹ i k) x :=
      ((Matrix.entryLinearMap ℝ ℝ i k).toContinuousLinearMap.hasFDerivAt.comp x hInv).differentiableAt
    rw [he'.fderiv_eq, fderiv_fun_mul hDet.differentiableAt hI]
    simp only [add_apply, smul_apply, smul_eq_mul, hdet, hinv, ← Finset.sum_mul]
    change (A x).det * -(∑ a, ∑ b, B i a * D i a b * B b k) +
      B i k * ((A x).det * ∑ a, ∑ b, B b a * D i a b) = _
    ring
  change (∑ i, fderiv ℝ (fun y => (A y).adjugate i k) x (axis i)) = 0
  simp only [hentry, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hSwap :
      (∑ i, ∑ a, ∑ b, B b a * D i a b * B i k) =
        ∑ i, ∑ a, ∑ b, B i a * D i a b * B b k := by
    calc
      _ = ∑ a, ∑ i, ∑ b, B b a * D i a b * B i k := Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, B i a * D b a i * B b k := by
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, B i a * D i a b * B b k := by
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun b _ => by rw [hs b a i]
      _ = _ := Finset.sum_comm
  rw [hSwap, sub_self, mul_zero]

theorem adjugate_jacobian_contraction
    (A D : Matrix ((I dim)) ((I dim)) ℝ) :
    (∑ i : (I dim), ∑ k : (I dim), A.adjugate i k *
      (∑ a : (I dim), A a i * D k a)) = A.det * ∑ k : (I dim), D k k := by
  have hAC (a k : (I dim)) :
      (∑ i : (I dim), A a i * A.adjugate i k) = A.det * (if a = k then 1 else 0) := by
    have h := congrArg (fun M : Matrix ((I dim)) ((I dim)) ℝ => M a k) (Matrix.mul_adjugate A)
    simpa only [Matrix.mul_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul] using h
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k : (I dim), ∑ a : (I dim),
        (∑ i : (I dim), A a i * A.adjugate i k) * D k a := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp_rw [hAC]
      simp [← Finset.mul_sum]

private theorem contDiff_adjugate_entry {A : (X dim) → (Mat dim)}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun y => A y i j)) (i j : (I dim)) :
    ContDiff ℝ ∞ (fun y => (A y).adjugate i j) := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply contDiffOn_univ.mp
  apply contDiffOn_det_of_entries (g := fun y => (A y).updateRow j (Pi.single i 1))
  intro a b
  by_cases h : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simpa only [Matrix.updateRow_apply,h,ite_false] using (hA a b).contDiffOn

theorem coordinateFluxDivergence_signedPiolaFlux
    (F Z : (X dim) → (X dim)) (hF : ContDiff ℝ ∞ F) (x : (X dim)) (hZ : DifferentiableAt ℝ Z (F x))
    (hJ : (coordinateJacobian F x).det ≠ 0) :
    coordinateFluxDivergence (signedPiolaFlux F Z) x =
      (coordinateJacobian F x).det * coordinateFluxDivergence Z (F x) := by
  let A := coordinateJacobian F
  let C : (X dim) → Matrix ((I dim)) ((I dim)) ℝ := fun y => (A y).adjugate
  let Zc (k : (I dim)) : (X dim) → ℝ := fun y => Z y k
  have hC (i k : (I dim)) : DifferentiableAt ℝ (fun y => C y i k) x :=
    (contDiff_adjugate_entry (fun a b => contDiff_coordinateJacobian_entry F hF a b) i k).differentiable
      (by simp) x
  have hZc (k : (I dim)) : DifferentiableAt ℝ (Zc k) (F x) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).differentiableAt.comp (F x) hZ
  have hZF (k : (I dim)) : DifferentiableAt ℝ (fun y => Zc k (F y)) x :=
    (hZc k).comp x (hF.differentiable (by simp) x)
  have hZFder (k i : (I dim)) :
      fderiv ℝ (fun y => Zc k (F y)) x (axis i) =
        ∑ a : (I dim), A x a i * fderiv ℝ (Zc k) (F x) (axis a) := by
    have h := (hZc k).hasFDerivAt.comp x
      (hF.differentiable (by simp) x).hasFDerivAt
    change fderiv ℝ ((Zc k) ∘ F) x (axis i) = _
    rw [h.fderiv]
    change fderiv ℝ (Zc k) (F x) (fderiv ℝ F x (axis i)) = _
    exact by
      rw [← vector_eq_sum_axis (fderiv ℝ F x (axis i)), map_sum]
      simp only [map_smul,smul_eq_mul, coordinateJacobian,coordinateMatrix_apply,A]
  have hterm (i k : (I dim)) :
      fderiv ℝ (fun y => C y i k * Zc k (F y)) x (axis i) =
        C x i k * fderiv ℝ (fun y => Zc k (F y)) x (axis i) +
          Zc k (F x) * fderiv ℝ (fun y => C y i k) x (axis i) := by
    rw [fderiv_fun_mul (hC i k) (hZF k)]
    rfl
  have hzero : (∑ i : (I dim), ∑ k : (I dim),
      Zc k (F x) * fderiv ℝ (fun y => C y i k) x (axis i)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hz (k : (I dim)) :
        (∑ i : (I dim), fderiv ℝ (fun y => C y i k) x (axis i)) = 0 :=
      coordinateJacobian_adjugate_column_divergence F hF x hJ k
    simp_rw [hz,mul_zero]
    exact Finset.sum_const_zero
  change (∑ i : (I dim), fderiv ℝ (fun y => ∑ k : (I dim), C y i k * Zc k (F y)) x
    (axis i)) = _
  have hsum (i : (I dim)) := fderiv_fun_sum (u := Finset.univ)
    (A := fun k y => C y i k * Zc k (F y)) (fun k _ => (hC i k).mul (hZF k))
  simp_rw [hsum]
  simp only [sum_apply]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  rw [hzero,add_zero]
  simp_rw [hZFder]
  exact adjugate_jacobian_contraction (A x)
    (fun k a => fderiv ℝ (Zc k) (F x) (axis a))

end CalderonN
