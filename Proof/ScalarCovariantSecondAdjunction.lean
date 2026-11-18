import Proof.ScalarCovariantSecondGreen
import Proof.ScalarCovariantAdjointNormalForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The explicit double covariant transpose is the genuine adjoint for
supported smooth sections and the actual local density. -/
theorem scalar_covariant_second_transpose_adjoint_data {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (mu : X → ℝ) (hmu : ContDiffOn ℝ ∞ mu Y) (hmuPos : ∀ x ∈ Y,0 < mu x)
    (a : X → Mat) (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (U V : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) :
    let I20 := (sphereSobolevInclusionL 1 0 (by norm_num)).comp
      (sphereSobolevInclusionL 2 1 (by norm_num))
    let L := fun x => mu x*⟪scalarCovariantSecondSection d a U x,I20 (V x)⟫_ℝ
    let R := fun x => mu x*⟪I20 (U x),scalarCovariantSecondTransposeSection d mu a V x⟫_ℝ
    Integrable L ∧ Integrable R ∧ (∫ x,L x)=(∫ x,R x) := by
  let I20 := (sphereSobolevInclusionL 1 0 (by norm_num)).comp
    (sphereSobolevInclusionL 2 1 (by norm_num))
  let L := fun i j x => mu x*a x i j*⟪oneSectionCovariantDerivative d
    (fun y => highSectionCovariantDerivative d U y (axis j)) x (axis i),I20 (V x)⟫_ℝ
  let R := fun i j x => ⟪I20 (U x),oneSectionCovariantDerivative d
    (fun y => highSectionCovariantDerivative d (fun z => (mu z*a z i j) • V z) y (axis i)) x (axis j)⟫_ℝ
  have hData (i j : I) : Integrable (L i j) ∧ Integrable (R i j) ∧
      (∫ x,L i j x)=(∫ x,R i j x) :=
    scalar_covariant_second_term_green_data hY d hg hK he (fun x => mu x*a x i j) U V S hS hSY
      (fun x hx => ((hmu.mul (ha i j)).contDiffAt (hY.mem_nhds (hSY hx)))) hU hV h0U h0V (axis i) (axis j)
  have hLeft (x : X) : mu x*⟪scalarCovariantSecondSection d a U x,I20 (V x)⟫_ℝ=
      ∑ i : I,∑ j : I,L i j x := by
    simp only [scalarCovariantSecondSection,sum_inner,real_inner_smul_left,Finset.mul_sum,L,mul_assoc]
  have hRight (x : X) : mu x*⟪I20 (U x),scalarCovariantSecondTransposeSection d mu a V x⟫_ℝ=
      ∑ i : I,∑ j : I,R i j x := by
    by_cases hx : x ∈ S
    · have hmu0 : mu x ≠ 0 := (hmuPos x (hSY hx)).ne'
      simp only [scalarCovariantSecondTransposeSection,inner_smul_right,inner_sum,
        ←mul_assoc,mul_inv_cancel₀ hmu0,one_mul,R]
    · simp only [h0U x hx,map_zero,inner_zero_left,mul_zero,R,Finset.sum_const_zero]
  have hLs : Integrable (fun x => ∑ i : I,∑ j : I,L i j x) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hData i j).1))
  have hRs : Integrable (fun x => ∑ i : I,∑ j : I,R i j x) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hData i j).2.1))
  refine ⟨hLs.congr (Eventually.of_forall (fun x => (hLeft x).symm)),
    hRs.congr (Eventually.of_forall (fun x => (hRight x).symm)),?_⟩
  calc
    _ = ∫ x,∑ i : I,∑ j : I,L i j x := integral_congr_ae (Eventually.of_forall hLeft)
    _ = ∑ i : I,∑ j : I,∫ x,L i j x := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hData i j).1))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => (hData i j).1)
    _ = ∑ i : I,∑ j : I,∫ x,R i j x := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (hData i j).2.2
    _ = ∫ x,∑ i : I,∑ j : I,R i j x := by
      symm
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hData i j).2.1))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => (hData i j).2.1)
    _ = _ := integral_congr_ae (Eventually.of_forall (fun x => (hRight x).symm))

end ShrinkingSpheres
