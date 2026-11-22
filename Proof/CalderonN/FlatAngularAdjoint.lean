module

public import Proof.CalderonN.FlatBallPolynomials
public import Proof.CalderonN.ParametricBallVelocityAdjoint

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! Adapted from `FlatAngularAdjoint` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Rotation derivatives depend only on values on the sphere. -/
theorem sphereRotationDerivative_congr_of_eqOn_sphere {f g : (X dim) → ℝ} {w : (X dim)}
    (hw : w ∈ (standardSphere dim)) (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w)
    (he : EqOn f g (standardSphere dim)) (i j : (I dim)) :
    sphereRotationDerivative i j f w = sphereRotationDerivative i j g w := by
  let p := fun t : ℝ => coordinateRotation i j t w
  have h₀ : p 0 = w := coordinateRotation_zero i j w
  have hp : HasDerivAt p (rotationVector i j w) 0 := by
    simpa only [p,coordinateRotation_zero] using hasDerivAt_coordinateRotation i j 0 w
  have hhF : DifferentiableAt ℝ f (p 0) := h₀.symm ▸ hf
  have hhG : DifferentiableAt ℝ g (p 0) := h₀.symm ▸ hg
  have hF := hhF.hasFDerivAt.comp_hasDerivAt 0 hp
  have hG := hhG.hasFDerivAt.comp_hasDerivAt 0 hp
  have he' : f ∘ p = g ∘ p := by
    funext t
    apply he
    apply mem_sphere_zero_iff_norm.mpr
    rw [show ‖p t‖ = ‖w‖ from coordinateRotation_norm i j t w]
    exact mem_sphere_zero_iff_norm.mp hw
  have h := (he' ▸ hF).unique hG
  simpa only [sphereRotationDerivative,h₀] using h

theorem conormalComponent_flat_affineVelocity {t : ℝ} (ht : 0 < t) (a : (X dim)) (b : ℝ)
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    conormalComponent (flatBallMetric t) w (a+b • w) = (flatLinear a w+b)/(t^(dim-2)) := by
  have h : ⟪w,w⟫_ℝ = 1 := flatRadiusSq_on_sphere hw
  rw [conormalComponent,ballConormalVector_flat ht,inner_add_right,
    real_inner_smul_right,real_inner_smul_right,h,mul_one,mul_one]
  exact congrArg (fun u : ℝ => (u+b)/(t^(dim-2))) (real_inner_comm a w)

theorem tangentialComponent_flat_affineVelocity {t : ℝ} (ht : 0 < t) (a : (X dim)) (b : ℝ)
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    tangentialComponent (flatBallMetric t) w (a+b • w) = a-flatLinear a w • w := by
  rw [tangentialComponent,conormalComponent_flat_affineVelocity ht a b hw,ballConormalVector_flat ht,
    smul_smul,div_mul_cancel₀ _ (pow_ne_zero _ ht.ne'),add_smul]
  abel

private theorem rotationVector_swap (i j : (I dim)) (w : (X dim)) :
    rotationVector j i w = -rotationVector i j w := by
  simp only [rotationVector,neg_sub]

private theorem sum_rotationDerivative_symm (f : (I dim) → (I dim) → (X dim) → ℝ)
    (hs : ∀ i j, f i j = f j i) (w : (X dim)) :
    ∑ i, ∑ j, sphereRotationDerivative i j (f i j) w = 0 := by
  let S := ∑ i, ∑ j, sphereRotationDerivative i j (f i j) w
  have h (i j : (I dim)) : sphereRotationDerivative j i (f j i) w =
      -sphereRotationDerivative i j (f i j) w := by
    rw [hs j i]
    unfold sphereRotationDerivative
    rw [rotationVector_swap i j,map_neg]
  have hh : S = -S := by
    dsimp only [S]
    calc
      _ = ∑ j, ∑ i, sphereRotationDerivative i j (f i j) w := Finset.sum_comm
      _ = ∑ i, ∑ j, -sphereRotationDerivative i j (f i j) w :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))
      _ = _ := by simp only [Finset.sum_neg_distrib]
  change S = 0
  linarith

private theorem rotationDerivative_coordinate (i j k : (I dim)) (w : (X dim)) :
    sphereRotationDerivative i j (fun z : (X dim) => z k) w = (rotationVector i j w) k := by
  let L := EuclideanSpace.proj (𝕜 := ℝ) k
  change fderiv ℝ L w (rotationVector i j w) = _
  rw [ContinuousLinearMap.fderiv]
  rfl

private theorem sum_rotationDerivative_translation (a w : (X dim)) :
    ∑ i, ∑ j, sphereRotationDerivative i j (fun z => z i * a j) w = (1-(dim : ℝ))*flatLinear a w := by
  have h (i j : (I dim)) : sphereRotationDerivative i j (fun z => z i * a j) w =
      (rotationVector i j w) i * a j := by
    let L := EuclideanSpace.proj (𝕜 := ℝ) i
    change fderiv ℝ (fun z => L z * a j) w (rotationVector i j w) = _
    rw [fderiv_mul_const L.differentiableAt]
    simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.fderiv]
    change a j * (rotationVector i j w) i = _
    ring
  simp only [h,flatLinear_eq_sum]
  rw [Finset.sum_comm]
  have hterm (i j : I dim) : (rotationVector i j w) i * a j =
      (if i = j then w j * a j else 0) - w j * a j := by
    by_cases hij : i = j
    · subst j
      simp [rotationVector]
    · simp [rotationVector,PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply,hij]
      <;> ring
  simp only [hterm,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => mul_comm (w j) (a j))]
  ring

/-- Integration by parts in the tangential portion of an affine
velocity has the explicit spherical divergence in dimension n. -/
theorem sum_rotationDerivative_flatVelocity {t : ℝ} (ht : 0 < t) (a : (X dim)) (b : ℝ)
    {φ : (X dim) → ℝ} (hφ : ContDiff ℝ ∞ φ) {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    (∑ i, ∑ j, sphereRotationDerivative i j
      (fun z => φ z * (z i * tangentialComponent (flatBallMetric t) z (a+b • z) j)) w) =
      fderiv ℝ φ w (a-flatLinear a w • w) + (1-(dim:ℝ))*flatLinear a w*φ w := by
  let T (z : (X dim)) := a-flatLinear a z • z
  let L (i j : (I dim)) (z : (X dim)) := z i * T z j
  have hT : ContDiff ℝ ∞ T := contDiff_const.sub ((contDiff_flatLinear a).smul contDiff_id)
  have hL (i j : (I dim)) : ContDiff ℝ ∞ (L i j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hT)
  let V (z : (X dim)) := a+b • z
  have hV' : ContDiff ℝ ∞ (fun z : (X dim) => b • z) := (b • ContinuousLinearMap.id ℝ (X dim)).contDiff
  have hV : ContDiff ℝ ∞ V := contDiff_const.add hV'
  have hcor : DifferentiableAt ℝ (fun z => conormalComponent (flatBallMetric t) z (V z)) w := by
    have h₁ : ContDiff ℝ ∞ (fun z => ⟪z,V z⟫_ℝ) := contDiff_id.inner ℝ hV
    have hC : ContDiff ℝ ∞ (ballConormalVector (flatBallMetric t)) :=
      contDiffOn_univ.mp (contDiffOn_ballConormalVector (smoothMetric_flatBallMetric (dim := dim) ht))
    have h₂ : ContDiff ℝ ∞ (fun z => ⟪z,ballConormalVector (flatBallMetric t) z⟫_ℝ) :=
      contDiff_id.inner ℝ hC
    have hN : ⟪w,ballConormalVector (flatBallMetric t) w⟫_ℝ ≠ 0 := by
      rw [ballConormalVector_flat ht,real_inner_smul_right,
        show ⟪w,w⟫_ℝ = 1 from flatRadiusSq_on_sphere hw,mul_one]
      exact pow_ne_zero _ ht.ne'
    change DifferentiableAt ℝ (fun z => ⟪z,V z⟫_ℝ / ⟪z,ballConormalVector (flatBallMetric t) z⟫_ℝ) w
    exact (h₁.contDiffAt.div h₂.contDiffAt hN).differentiableAt (by simp)
  have hTan : DifferentiableAt ℝ (fun z => tangentialComponent (flatBallMetric t) z (V z)) w :=
    (hV.differentiable (by simp) _).sub (hcor.smul
      ((contDiffOn_univ.mp (contDiffOn_ballConormalVector (smoothMetric_flatBallMetric (dim := dim) ht))).differentiable
        (by simp) _))
  have hTanComp (j : (I dim)) : DifferentiableAt ℝ (fun z => tangentialComponent (flatBallMetric t) z (V z) j) w :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.comp w hTan
  have hφw := hφ.differentiable (by simp) w
  have hcong (i j : (I dim)) :
      sphereRotationDerivative i j
        (fun z => φ z * (z i * tangentialComponent (flatBallMetric t) z (V z) j)) w =
        sphereRotationDerivative i j (fun z => φ z * L i j z) w := by
    apply sphereRotationDerivative_congr_of_eqOn_sphere hw
      (hφw.mul ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.mul (hTanComp j)))
      (hφw.mul ((hL i j).differentiable (by simp) w)) _ i j
    intro z hz
    simp [L,T,V,tangentialComponent_flat_affineVelocity ht a b hz]
  have hmul (i j : (I dim)) : sphereRotationDerivative i j (fun z => φ z * L i j z) w =
      φ w * sphereRotationDerivative i j (L i j) w +
        L i j w * fderiv ℝ φ w (rotationVector i j w) := by
    unfold sphereRotationDerivative
    rw [fderiv_fun_mul hφw ((hL i j).differentiable (by simp) w)]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  have hSplit (i j : (I dim)) : sphereRotationDerivative i j (L i j) w =
      sphereRotationDerivative i j (fun z => z i*a j) w -
        sphereRotationDerivative i j (fun z => z i*flatLinear a z*z j) w := by
    have he : L i j = (fun z => z i*a j) - (fun z => z i*flatLinear a z*z j) := by
      funext z
      simp only [L,T,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,Pi.sub_apply]
      ring
    let P := EuclideanSpace.proj (𝕜 := ℝ) i
    let Q := EuclideanSpace.proj (𝕜 := ℝ) j
    have h₁ : DifferentiableAt ℝ (fun z : (X dim) => z i * a j) w := P.differentiableAt.mul_const _
    have h₂ : DifferentiableAt ℝ (fun z : (X dim) => z i * flatLinear a z * z j) w :=
      (P.differentiableAt.mul ((contDiff_flatLinear a).differentiable (by simp) _)).mul Q.differentiableAt
    simp only [sphereRotationDerivative,he,fderiv_sub h₁ h₂,_root_.sub_apply]
  have hSum : ∑ i, ∑ j, sphereRotationDerivative i j (L i j) w = (1-(dim : ℝ))*flatLinear a w := by
    simp_rw [hSplit]
    simp only [Finset.sum_sub_distrib,sum_rotationDerivative_translation]
    have h := sum_rotationDerivative_symm (fun i j z => z i*flatLinear a z*z j)
      (fun i j => funext (fun z => by ring)) w
    rw [h,sub_zero]
  have hTanSum : ∑ i, ∑ j, L i j w • rotationVector i j w = T w := by
    change (∑ i, ∑ j, (w i * T w j) • rotationVector i j w) = _
    rw [sum_rotationVector_smul]
    have hN : ⟪w,w⟫_ℝ = 1 := flatRadiusSq_on_sphere hw
    have hOrth : ⟪w,T w⟫_ℝ = 0 := by
      change ⟪w,a-flatLinear a w • w⟫_ℝ = 0
      rw [inner_sub_right,real_inner_smul_right,hN,mul_one,flatLinear,real_inner_comm a w,sub_self]
    rw [hN,hOrth,one_smul,zero_smul,sub_zero]
  change (∑ i, ∑ j, sphereRotationDerivative i j
    (fun z => φ z * (z i * tangentialComponent (flatBallMetric t) z (V z) j)) w) = _
  simp_rw [hcong,hmul]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,hSum]
  have hD : ∑ i, ∑ j, L i j w * fderiv ℝ φ w (rotationVector i j w) = fderiv ℝ φ w (T w) := by
    rw [← hTanSum]
    simp [map_sum,map_smul,smul_eq_mul]
  rw [hD]
  dsimp only [T]
  ring

end CalderonN
