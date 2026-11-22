module

public import Proof.CalderonN.SupportedSphereMultiplierFamily
public import Proof.CalderonN.ActualSupportedConormal

import Proof.CalderonN.FixedBallSmoothFlux
import Proof.CalderonN.ParametricBallConormal
import Mathlib.Tactic

/-! Joint regularity of the genuine velocity and inverse conormal
weight multipliers, allowing the coefficients in the Gauss adjoint
to be transposed on the same smooth section space. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

@[expose] def conormalWeightQuadratic (A : Mat dim) (z : X dim) : ℝ :=
  ∑ i : I dim,z i*(∑ j : I dim,A i j*z j)

omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem conormalWeightQuadratic_pos {A : Mat dim} (hA : A.PosDef)
    {z : X dim} (hz : z ≠ 0) :
    0 < conormalWeightQuadratic A z := by
  have hZ : (fun i : I dim => z i) ≠ 0 := by
    intro h
    apply hz
    ext i
    exact congrFun h i
  have h := hA.dotProduct_mulVec_pos hZ
  simpa only [conormalWeightQuadratic,dotProduct,Matrix.mulVec,star_trivial,Pi.star_apply] using h

omit [Nontrivial (Fin dim)] in
theorem ActualGaussFiberData.weight_eq_quadratic {x : X dim} (D : ActualGaussFiberData d x)
    {z : X dim} (hz : z ∈ standardSphere dim) :
    D.weight.1 z = conormalWeightQuadratic (D.coefficient z) z := by
  let L : X dim →L[ℝ] ℝ := innerSL ℝ z
  let u : SmoothData dim := ⟨L,L.contDiff⟩
  have hL : fderiv ℝ u.1 z z = 1 := by
    change fderiv ℝ (⇑L) z z = 1
    rw [L.fderiv]
    change ⟪z,z⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp hz,one_pow]
  have hC (i : I dim) : coordDeriv i u.1 z = z i := by
    change fderiv ℝ (⇑L) z (axis i) = _
    rw [L.fderiv]
    simp only [L,innerSL_apply_apply,axis,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
  have h := D.weightConormal u hz
  change smoothBallConormal D.coefficient u.1 z = D.weight.1 z*fderiv ℝ u.1 z z at h
  rw [hL,mul_one] at h
  rw [← h]
  simp only [smoothBallConormal,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
    smoothBallFlux_apply,conormalWeightQuadratic,hC]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem actualReciprocalSphereMultiplier_regular (hY : IsOpen Y)
    (D : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hLoc : ∀ x ∈ Y,∃ (V : Set (X dim)) (A : X dim × X dim → Mat dim),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Y ∧ ContDiff ℝ ∞ A ∧
      ∀ y ∈ V,∀ hy : y ∈ Y,EqOn (fun z => A (y,z)) (D y hy).coefficient (closedBall (0:X dim) 1))
    (hPos : ∀ x (hx : x ∈ Y),∀ z ∈ standardSphere dim,((D x hx).coefficient z).PosDef) :
    SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily (fun x hx => (D x hx).reciprocal)) := by
  apply supportedSphereMultiplierFamily_regular hY
  intro x hx
  obtain ⟨V,A,hV,hxV,hVY,hA,hEq⟩ := hLoc x hx
  let Z : Set (X dim) := {0}ᶜ
  let f (p : X dim × X dim) := conormalWeightQuadratic (A p) p.2
  let R (p : X dim × X dim) := (p.1,sphereNormalize p.2)
  have hR : ContDiffOn ℝ ∞ R (V ×ˢ Z) :=
    contDiff_fst.contDiffOn.prodMk (contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn (fun _ h => h.2))
  have hf : ContDiff ℝ ∞ f := by
    unfold f conormalWeightQuadratic
    apply ContDiff.sum
    intro i _
    apply ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp contDiff_snd).mul
    exact ContDiff.sum fun j _ => (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp contDiff_snd)
  have hN : ∀ p ∈ V ×ˢ Z,(f ∘ R) p ≠ 0 := by
    intro p hp
    let z := sphereNormalize p.2
    have hz := sphereNormalize_mem_sphere hp.2
    have hZ0 : z ≠ 0 := by
      intro h
      have hh : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
      rw [h,norm_zero] at hh
      exact zero_ne_one hh
    have hA' : A (p.1,z) = (D p.1 (hVY hp.1)).coefficient z :=
      hEq p.1 hp.1 (hVY hp.1) (sphere_subset_closedBall hz)
    change conormalWeightQuadratic (A (p.1,z)) z ≠ 0
    rw [hA']
    exact (conormalWeightQuadratic_pos (hPos p.1 (hVY hp.1) z hz) hZ0).ne'
  refine ⟨V,(f ∘ R)⁻¹,hV,hxV,hVY,(hf.comp_contDiffOn hR).inv hN,?_⟩
  intro y hy hyY z hz
  change (conormalWeightQuadratic (A (y,sphereNormalize z)) (sphereNormalize z))⁻¹ = _
  have hAZ : A (y,z) = (D y hyY).coefficient z := hEq y hy hyY (sphere_subset_closedBall hz)
  have hInv : (D y hyY).reciprocal.1 z = ((D y hyY).weight.1 z)⁻¹ := (D y hyY).reciprocalEq hz
  rw [sphereNormalize_eq_of_sphere hz,hAZ,← (D y hyY).weight_eq_quadratic hz,hInv]

theorem actualVelocitySphereMultipliers_regular (hY : IsOpen Y)
    (D : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim)
    (V : X dim × X dim → X dim)
    (hV : ∀ p ∈ Y ×ˢ standardSphere dim,ContDiffAt ℝ ∞ V p)
    (hEq : ∀ x (hx : x ∈ Y),∀ z ∈ standardSphere dim,((D x hx).velocity i).1 z = V (x,z)) :
    SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => smoothVelocityNormal ((D x hx).velocity i))) ∧
    ∀ a b : I dim,SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => smoothVelocityAngular ((D x hx).velocity i) a b)) := by
  let Z : Set (X dim) := {0}ᶜ
  let R (p : X dim × X dim) := (p.1,sphereNormalize p.2)
  have hR : ContDiffOn ℝ ∞ R (Y ×ˢ Z) :=
    contDiff_fst.contDiffOn.prodMk (contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn (fun _ h => h.2))
  have hA : ContDiffOn ℝ ∞ (V ∘ R) (Y ×ˢ Z) := by
    intro p hp
    exact (hV (R p) ⟨hp.1,sphereNormalize_mem_sphere hp.2⟩).comp_contDiffWithinAt p (hR p hp)
  constructor
  · apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    refine ⟨Y,fun p => ⟪p.2,V (R p)⟫_ℝ,hY,hx,Subset.rfl,
      contDiff_snd.contDiffOn.inner ℝ hA,?_⟩
    intro y hy hyY z hz
    change ⟪z,V (y,sphereNormalize z)⟫_ℝ = ⟪z,((D y hyY).velocity i).1 z⟫_ℝ
    rw [sphereNormalize_eq_of_sphere hz,hEq y hyY z hz]
  · intro a b
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    refine ⟨Y,fun p => p.2 a*V (R p) b,hY,hx,Subset.rfl,?_,?_⟩
    · exact ((EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.comp contDiff_snd).contDiffOn.mul
        ((EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.comp_contDiffOn hA)
    intro y hy hyY z hz
    change z a*V (y,sphereNormalize z) b = z a*((D y hyY).velocity i).1 z b
    rw [sphereNormalize_eq_of_sphere hz,hEq y hyY z hz]

end CalderonN
