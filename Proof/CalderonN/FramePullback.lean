module

public import Proof.CalderonN.SphereDerivativeCongruence
public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.MetricConnection

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set Filter
namespace CalderonN
variable {N : ℕ}
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Infinitesimal rotation of frame coordinates under parallel transport. -/
def frameAngularVector (A : (I N) → (I N) → ℝ) (z : (X N)) : (X N) :=
  ∑ i,∑ j,(-A i j*z i) • axis j

lemma frameAngularVector_eq_rotation (A : (I N) → (I N) → ℝ) (hA : ∀ i j,A i j = -A j i) (z : (X N)) :
    frameAngularVector A z = ∑ i,∑ j,(-(1/2 : ℝ)*A i j) • rotationVector i j z := by
  have hv (i j : I N) :
      rotationVector i j z = z i • axis j - z j • axis i := rfl
  have hswap :
      (∑ i, ∑ j, (-(1/2 : ℝ)*A i j * z j) • axis i) =
        -(∑ i, ∑ j, (-(1/2 : ℝ)*A i j * z i) • axis j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← neg_smul, hA j i]
    congr 1
    ring
  simp only [hv, smul_sub, smul_smul, Finset.sum_sub_distrib, hswap, sub_neg_eq_add]
  rw [← Finset.sum_add_distrib]
  unfold frameAngularVector
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_smul]
  congr 1
  ring

def frameVectorLinear (e : (Frame N)) (y : (X N)) : (X N) →L[ℝ] (X N) :=
  ∑ i,(EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (e y i)

lemma frameVectorLinear_apply (e : (Frame N)) (y z : (X N)) : frameVectorLinear e y z = frameVector e y z := by
  simp [frameVectorLinear,frameVector,PiLp.proj_apply]

lemma frameVector_axis (e : (Frame N)) (y : (X N)) (i : (I N)) : frameVector e y (axis i) = e y i := by
  simp [frameVector,axis]

lemma frameVector_frameAngularVector (g : (MetricField N)) (e : (Frame N)) (y a z : (X N))
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    frameVector e y (frameAngularVector (frameConnectionCoefficient g e y a) z) =
      -(∑ i,z i • covariantFrameVector g e y a i) := by
  have hrec (i : (I N)) : (∑ j,frameConnectionCoefficient g e y a i j • e y j) =
      covariantFrameVector g e y a i := by
    exact frameVector_frameCoordinates g y (covariantFrameVector g e y a i) (e y) hframe
  rw [← frameVectorLinear_apply,frameAngularVector,map_sum]
  simp_rw [map_sum,map_smul,frameVectorLinear_apply,frameVector_axis]
  have ht (i j : (I N)) : (-frameConnectionCoefficient g e y a i j*z i) • e y j =
      -(z i • (frameConnectionCoefficient g e y a i j • e y j)) := by
    rw [smul_smul,← neg_smul]
    congr 1
    ring
  simp_rw [ht,Finset.sum_neg_distrib,← Finset.smul_sum,hrec]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_frame_pullback_apply (e : (Frame N)) (F : (X N) × (X N) → E) (y z a b : (X N))
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hF : DifferentiableAt ℝ F (y,frameVector e y z)) :
    fderiv ℝ (fun q : (X N) × (X N) => F (q.1,frameVector e q.1 q.2)) (y,z) (a,b) =
      fderiv ℝ F (y,frameVector e y z) (a,frameVector e y b+∑ i,z i • fderiv ℝ (fun x => e x i) y a) := by
  have hfst := hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,z))
  have hsnd := hasFDerivAt_snd (𝕜:=ℝ) (p:=(y,z))
  have hZ (i : (I N)) := (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt.comp (y,z) hsnd
  have hE (i : (I N)) := (he i).hasFDerivAt.comp (y,z) hfst
  have hs := HasFDerivAt.sum (u:=Finset.univ) (fun i _ => (hZ i).smul (hE i))
  have hfun : (fun q : X N × X N => frameVector e q.1 q.2) =
      ∑ i : I N, (EuclideanSpace.proj (𝕜 := ℝ) i ∘ (Prod.snd : X N × X N → X N)) • ((fun t => e t i) ∘ Prod.fst) := by
    funext q
    simp only [frameVector, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [← hfun] at hs
  have hp := hfst.prodMk hs
  have hh := hF.hasFDerivAt.comp (y,z) hp
  change HasFDerivAt (fun q : (X N) × (X N) => F (q.1,frameVector e q.1 q.2)) _ (y,z) at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst',_root_.sum_apply,_root_.add_apply,
    ContinuousLinearMap.smulRight_apply,_root_.smul_apply,ContinuousLinearMap.coe_snd',
    PiLp.proj_apply,Function.comp_apply,← Finset.sum_add_distrib,frameVector]
  simp only [add_comm]

/-- The actual horizontal derivative pulls back to the covariant base/angular derivative. -/
theorem horizontal_eq_frame_pullback (g : (MetricField N)) (e : (Frame N)) (F : (X N) × (X N) → E) (y z a : (X N))
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hF : DifferentiableAt ℝ F (y,frameVector e y z)) :
    horizontal g F y (frameVector e y z) a =
      fderiv ℝ (fun q : (X N) × (X N) => F (q.1,frameVector e q.1 q.2)) (y,z)
        (a,frameAngularVector (frameConnectionCoefficient g e y a) z) := by
  rw [fderiv_frame_pullback_apply e F y z a _ he hF,
    frameVector_frameAngularVector g e y a z hframe]
  have hconn : connection g y a (frameVector e y z) = ∑ i,z i • connection g y a (e y i) := by
    simp only [frameVector,← connectionBilinear_apply,map_sum,map_smul]
  have heq : -(∑ i,z i • covariantFrameVector g e y a i)+∑ i,z i • fderiv ℝ (fun x => e x i) y a =
      -connection g y a (frameVector e y z) := by
    rw [hconn]
    simp only [covariantFrameVector,smul_add,Finset.sum_add_distrib]
    abel
  rw [heq]
  rfl

lemma differentiableAt_frame_pullback (e : (Frame N)) (F : (X N) × (X N) → E) (y z : (X N))
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hF : DifferentiableAt ℝ F (y,frameVector e y z)) :
    DifferentiableAt ℝ (fun q : (X N) × (X N) => F (q.1,frameVector e q.1 q.2)) (y,z) := by
  have hp : DifferentiableAt ℝ (fun q : (X N) × (X N) => (q.1,frameVector e q.1 q.2)) (y,z) := by
    apply differentiableAt_fst.prodMk
    have hfst := hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,z))
    have hE' (i : (I N)) := (he i).hasFDerivAt.comp (y,z) hfst
    have hE (i : (I N)) : DifferentiableAt ℝ (fun q : (X N) × (X N) => e q.1 i) (y,z) := (hE' i).differentiableAt
    exact DifferentiableAt.fun_sum (fun i _ =>
      ((EuclideanSpace.proj (𝕜:=ℝ) i).differentiableAt.comp (y,z) differentiableAt_snd).smul (hE i))
  exact hF.comp (y,z) hp

/-- Covariant base/angular differentiation depends only on the values on the sphere bundle. -/
lemma fderiv_covariant_eq_of_eqOn_spheres {Y : Set (X N)} (hY : IsOpen Y) {y : (X N)} (hy : y ∈ Y)
    (z : (UnitSphere N)) (F G : (X N) × (X N) → E) (hF : DifferentiableAt ℝ F (y,z.val))
    (hG : DifferentiableAt ℝ G (y,z.val))
    (hEq : ∀ x ∈ Y,∀ w : (UnitSphere N),F (x,w.val) = G (x,w.val))
    (A : (I N) → (I N) → ℝ) (hA : ∀ i j,A i j = -A j i) (a : (X N)) :
    fderiv ℝ F (y,z.val) (a,frameAngularVector A z.val) =
      fderiv ℝ G (y,z.val) (a,frameAngularVector A z.val) := by
  have hv : (0,frameAngularVector A z.val) =
      ∑ i,∑ j,(-(1/2 : ℝ)*A i j) • ((0 : (X N)),rotationVector i j z.val) := by
    have hh := congrArg (ContinuousLinearMap.inr ℝ (X N) (X N)) (frameAngularVector_eq_rotation A hA z.val)
    simpa only [map_sum,map_smul,ContinuousLinearMap.inr_apply] using hh
  have hp : (a,frameAngularVector A z.val) = (a,0)+(0,frameAngularVector A z.val) := by simp
  rw [hp,map_add,map_add,fderiv_base_eq_of_eqOn_spheres hY hy z F G hF hG hEq a]
  congr 1
  rw [hv,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,map_smul,fderiv_vertical_rotation_eq_of_eqOn_spheres y z F G hF hG (hEq y hy) i j]

end CalderonN
