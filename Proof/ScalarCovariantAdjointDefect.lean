import Proof.ScalarCovariantAdjointNormalForm
import Proof.LocalScalarAdjointSmoothness
import Proof.SupportedCovariantSections
import Proof.HalfCovariantEnergyControl
import Proof.Archive.ScalarSelfFormBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint
open OperatorForms

def scalarCovariantAdjointDefectSection (d : Data) (mu : X → ℝ) (a : MetricField)
    (U : X → SphereSobolev 2) (y : X) : SphereSobolev 0 :=
  adjointZeroCoefficient axis mu a y • sphereSobolevInclusionL 1 0 (by norm_num)
    (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
  ∑ i : I,adjointFirstCoefficient axis mu a y i • sphereSobolevInclusionL 1 0 (by norm_num)
    (highSectionCovariantDerivative d U y (axis i))

lemma scalarCovariantSecondTransposeSection_eq_add_defect {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (mu : X → ℝ) (hmu : ContDiffOn ℝ ∞ mu Y)
    (a : MetricField) (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (hSym : ∀ x ∈ Y,(a x).IsHermitian) (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) (hmu0 : mu y ≠ 0) :
    scalarCovariantSecondTransposeSection d mu a U y=
      scalarCovariantSecondSection d a U y+scalarCovariantAdjointDefectSection d mu a U y := by
  have hh := scalarCovariantSecondTransposeSection_sub hY d hg hK he mu hmu a ha hSym U hU hy hmu0
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

lemma scalarCovariantAdjointDefectSection_zero_off (d : Data) (mu : X → ℝ) (a : MetricField)
    (U : X → SphereSobolev 2) (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0)
    (x : X) (hx : x ∉ S) : scalarCovariantAdjointDefectSection d mu a U x=0 := by
  have hD (v : X) := highSectionCovariantDerivative_zero_off d U S hS h0 v x hx
  simp only [scalarCovariantAdjointDefectSection,h0 x hx,hD,map_zero,smul_zero,Finset.sum_const_zero,add_zero]

theorem contDiff_supported_scalarCovariantAdjointDefectSection {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (mu : X → ℝ) (hmu : ContDiffOn ℝ ∞ mu Y) (hpos : ∀ x ∈ Y,mu x ≠ 0)
    (a : MetricField) (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) :
    ContDiff ℝ ∞ (scalarCovariantAdjointDefectSection d mu a U) ∧
      ∀ x ∉ S,scalarCovariantAdjointDefectSection d mu a U x=0 := by
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let I20 := I10.comp (sphereSobolevInclusionL 2 1 (by norm_num))
  have hU0 : ContDiff ℝ ∞ (fun x => I20 (U x)) := I20.contDiff.comp hU
  have hU0off (x : X) (hx : x ∉ S) : I20 (U x)=0 := by rw [h0 x hx,map_zero]
  have hCS := contDiffOn_adjointZeroCoefficient hY mu a hmu ha hpos
  have hCZ : ContDiff ℝ ∞ (fun x => adjointZeroCoefficient axis mu a x • I20 (U x)) :=
    contDiff_supported_smul _ _ S hS hU0 hU0off (fun x hx => hCS.contDiffAt (hY.mem_nhds (hSY hx)))
  have hBS (i : I) := contDiffOn_adjointFirstCoefficient hY mu a hmu ha hpos i
  have hBZ (i : I) : ContDiff ℝ ∞ (fun x => adjointFirstCoefficient axis mu a x i •
      I10 (highSectionCovariantDerivative d U x (axis i))) := by
    have hHD := contDiff_supported_highSectionCovariantDerivative hY d hg hK he U hU S hS hSY h0 (axis i)
    exact contDiff_supported_smul _ _ S hS (I10.contDiff.comp hHD.1)
      (fun x hx => by rw [hHD.2 x hx,map_zero])
      (fun x hx => (hBS i).contDiffAt (hY.mem_nhds (hSY hx)))
  refine ⟨hCZ.add (ContDiff.sum (fun i _ => hBZ i)),?_⟩
  exact scalarCovariantAdjointDefectSection_zero_off d mu a U S hS h0

/-- A genuine contractive angular inclusion and three actual first
sections control the scalar first/zero defect square. -/
theorem scalar_first_zero_packet_norm_sq_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : F →L[ℝ] E) (hJ : ‖J‖ ≤ 1) (u : F) (V : I → E) (b : I → ℝ) (c B Z ε β : ℝ)
    (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hb : ∀ i,|b i| ≤ B*ε/β) (hc : |c| ≤ Z*ε) :
    ‖c • J u+∑ i : I,b i • V i‖^2 ≤
      (6*B^2+2*Z^2)*ε^2*(β⁻¹*(∑ i : I,‖V i‖^2)+β*‖u‖^2) := by
  let G := ∑ i : I,‖V i‖^2
  have hG : 0 ≤ G := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hβpos := zero_lt_one.trans_le hβ
  have hJN : ‖J u‖ ≤ ‖u‖ := (J.le_opNorm u).trans
    ((mul_le_mul_of_nonneg_right hJ (norm_nonneg u)).trans_eq (one_mul _))
  have hM : ‖c • J u‖^2 ≤ (Z*ε)^2*‖u‖^2 := by
    have hh : ‖c • J u‖ ≤ (Z*ε)*‖u‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hc hJN (norm_nonneg _) (mul_nonneg hZ hε)
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh).trans_eq (mul_pow _ _ 2)
  have hS : ‖∑ i : I,b i • V i‖^2 ≤ 3*(B*ε/β)^2*G :=
    norm_real_weighted_sum_three_sq_le b V (B*ε/β) (by positivity) hb
  have hInv : β⁻¹^2 ≤ β⁻¹ :=
    OAI.AnisotropicCalderon.ActualScalarPrincipalSelfFormBound.inv_sq_le_inv_of_one_le β hβ
  have hGS : (B*ε/β)^2*G ≤ (B^2*ε^2*β⁻¹)*G := by
    apply mul_le_mul_of_nonneg_right _ hG
    have hh := mul_le_mul_of_nonneg_left hInv (sq_nonneg (B*ε))
    convert hh using 1 <;> simp only [div_eq_mul_inv,mul_pow] <;> ring
  have hNS : (Z*ε)^2*‖u‖^2 ≤ (Z^2*ε^2*β)*‖u‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hβ (by positivity : 0 ≤ (Z*ε)^2*‖u‖^2)
    convert hh using 1 <;> ring
  have hAdd := OAI.AnisotropicCalderon.ActualScalarPrincipalSelfFormBound.norm_add_sq_le_twice
    (c • J u) (∑ i : I,b i • V i)
  have hx1 : 0 ≤ B^2*ε^2*β*‖u‖^2 := by positivity
  have hx2 : 0 ≤ Z^2*ε^2*β⁻¹*G := by positivity
  dsimp only [G] at hS hGS hx2
  nlinarith only [hAdd,hM,hS,hGS,hNS,hx1,hx2]

end ShrinkingSpheres
