import Proof.ParallelNormAssemblyReservedScalarPairPoint
import Proof.SupportedHalfCovariantSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma symmetric_skew_quadratic_gradient_zero
    (q : I → I → ℝ) (hq : ∀ a b,q a b=q b a)
    (D : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hSkew : ∀ u v : SphereSobolev (3/2:ℝ),sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (D v)=
      -sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) (D u))
    (H : I → SphereSobolev (3/2:ℝ)) :
    (∑ a : I,∑ b : I,q a b*sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b)) (D (H a)))=0 := by
  let S := ∑ a : I,∑ b : I,q a b*sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b)) (D (H a))
  have hNeg : S= -S := by
    calc
      S = ∑ a : I,∑ b : I,q b a*sphereSobolevDualPairing (1/2:ℝ)
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H a)) (D (H b)) := Finset.sum_comm
      _ = ∑ a : I,∑ b : I,-(q a b*sphereSobolevDualPairing (1/2:ℝ)
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b)) (D (H a))) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact (congrArg₂ (fun r t : ℝ => r*t) (hq b a) (hSkew (H a) (H b))).trans (mul_neg _ _)
      _ = -S := by simp only [S,Finset.sum_neg_distrib]
  change S=0
  linarith only [hNeg]

def scalarQuadraticSecondDensity (d : Data) (q : I → I → X → ℝ)
    (D : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ)) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ a : I,∑ b : I,q a b y*sphereSobolevDualPairing (1/2:ℝ)
    (halfSectionCovariantDerivativeL d (H b) y (axis a))
    (D y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))

def scalarQuadraticSecondRemainder (q : I → I → X → ℝ)
    (D : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (DQ : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ)) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ a : I,∑ b : I,(-q a b y*sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b y))
    (DQ a y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))-
    fderiv ℝ (q a b) y (axis a)*sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b y))
      (D y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))))

/-- The scalar-second versus skew quadratic angular part has one exact
Green reduction. The symmetric gradient square cancels BEFORE norms;
all integrability is proved using genuine supported sources first. -/
theorem symmetric_scalar_quadratic_green_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : I → I → X → ℝ) (hq : ∀ a b,ContDiffOn ℝ ∞ (q a b) Y)
    (hSym : ∀ y ∈ Y,∀ a b,q a b y=q b a y)
    (D : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (hD : ContDiffOn ℝ ∞ D Y)
    (hSkew : ∀ y ∈ Y,∀ u v : SphereSobolev (3/2:ℝ),sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (D y v)=
      -sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) (D y u))
    (DQ : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hDQ : ∀ a y,y ∈ Y → quadraticOperatorCovariantDerivativeL d D y (axis a)=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        ((DQ a y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (H : I → X → SphereSobolev (3/2:ℝ)) (hH : ∀ b,ContDiff ℝ ∞ (H b))
    (hHActual : ∀ a y,y ∈ Y → H a y=fiveHalfSectionCovariantDerivativeL d U y (axis a))
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hU0 : ∀ x ∉ S,U x=0) (hH0 : ∀ b x,x ∉ S → H b x=0) :
    IntegrableOn (scalarQuadraticSecondDensity d q D H U) Y ∧
    IntegrableOn (scalarQuadraticSecondRemainder q D DQ H U) Y ∧
    (∫ y in Y,scalarQuadraticSecondDensity d q D H U y)=
      ∫ y in Y,scalarQuadraticSecondRemainder q D DQ H U y := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let G := fun a b => quadraticWeakLeftPairDensity d (q a b) D (fun x => J (H b x)) (H b) U (axis a)
  let GT := fun y => ∑ a : I,∑ b : I,G a b y
  have hData (a b : I) := quadratic_weak_left_pair_weighted_data hY d (q a b) (hq a b) D hD
    (fun x => J (H b x)) (H b) (fun _ _ => rfl) U (J.contDiff.comp (hH b)) hU S hS hSY
    (fun x hx => by rw [hH0 b x hx,map_zero]) hU0 (axis a)
  have hGI : IntegrableOn GT Y := integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hData a b).1))
  have hLI (a b : I) : IntegrableOn (fun y => q a b y*sphereSobolevDualPairing (1/2:ℝ)
      (halfSectionCovariantDerivativeL d (H b) y (axis a)) (D y (U3 y))) Y := by
    have hh := contDiff_supported_halfSectionCovariantDerivative hY d hg hK he (H b) (hH b)
      S hS.isClosed hSY (hH0 b) (axis a)
    have hU3 : ContDiff ℝ ∞ U3 := (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp hU
    have hU30 (x : X) (hx : x ∉ S) : U3 x=0 := by simp only [U3,hU0 x hx,map_zero]
    exact (OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) (q a b) _ U3 D S hS
      (fun x hx => (hq a b).contDiffAt (hY.mem_nhds (hSY hx))) hh.1 hU3 hU30
      (fun x hx => hD.contDiffAt (hY.mem_nhds (hSY hx)))).integrableOn
  have hLT : IntegrableOn (scalarQuadraticSecondDensity d q D H U) Y :=
    integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hLI a b))
  have hEq : (fun y => scalarQuadraticSecondDensity d q D H U y-GT y)=ᵐ[volume.restrict Y]
      scalarQuadraticSecondRemainder q D DQ H U := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hGrad := symmetric_skew_quadratic_gradient_zero (fun a b => q a b y) (hSym y hy)
      (D y) (hSkew y hy) (fun b => H b y)
    have hRow (a b : I) := quadratic_weak_derivative_source_point d (q a b) D (H b) U y (axis a)
      ((hH b).differentiable (by simp) y) (DQ a y) (hDQ a y hy)
    have hRows (a b : I) : G a b y=
        q a b y*sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d (H b) y (axis a)) (D y (U3 y))+
        q a b y*sphereSobolevDualPairing (1/2:ℝ) (J (H b y)) (D y (H a y))-
        (-q a b y*sphereSobolevDualPairing (1/2:ℝ) (J (H b y)) (DQ a y (U3 y))-
          fderiv ℝ (q a b) y (axis a)*sphereSobolevDualPairing (1/2:ℝ) (J (H b y)) (D y (U3 y))) := by
      have hr := hRow a b
      rw [←hHActual a y hy] at hr
      dsimp only [G]
      rw [hr]
      dsimp only [J,U3]
      ring
    simp only [GT,hRows,scalarQuadraticSecondDensity,scalarQuadraticSecondRemainder,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
    dsimp only [J,U3] at hGrad ⊢
    rw [hGrad]
    ring
  have hRT : IntegrableOn (scalarQuadraticSecondRemainder q D DQ H U) Y := (hLT.sub hGI).congr hEq
  have hG0 : (∫ y in Y,GT y)=0 := by
    change (∫ y in Y,∑ a : I,∑ b : I,G a b y)=0
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hData a b).1))]
    apply Finset.sum_eq_zero
    intro a _
    rw [integral_finsetSum _ (fun b _ => (hData a b).1)]
    apply Finset.sum_eq_zero
    intro b _
    exact (hData a b).2
  refine ⟨hLT,hRT,?_⟩
  have hh := integral_congr_ae hEq
  rw [integral_sub hLT hGI,hG0,sub_zero] at hh
  exact hh

end ShrinkingSpheres.ParallelEnergy
