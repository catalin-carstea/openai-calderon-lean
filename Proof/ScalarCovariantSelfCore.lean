import Proof.ScalarCovariantAdjointDefect

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms

lemma scalarCovariantSecondSection_zero_off (d : Data) (a : MetricField)
    (U : X → SphereSobolev 2) (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0)
    (x : X) (hx : x ∉ S) : scalarCovariantSecondSection d a U x=0 := by
  have hD (j : I) := highSectionCovariantDerivative_zero_off d U S hS h0 (axis j)
  have hDD (i j : I) := oneSectionCovariantDerivative_zero_off d
    (fun y => highSectionCovariantDerivative d U y (axis j)) S hS (hD j) (axis i) x hx
  simp only [scalarCovariantSecondSection,hDD,smul_zero,Finset.sum_const_zero]

lemma scalarCovariantSecondTransposeSection_zero_off (d : Data) (mu : X → ℝ) (a : MetricField)
    (U : X → SphereSobolev 2) (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0)
    (x : X) (hx : x ∉ S) : scalarCovariantSecondTransposeSection d mu a U x=0 := by
  have hV (i j : I) (z : X) (hz : z ∉ S) : (mu z*a z i j) • U z=0 := by rw [h0 z hz,smul_zero]
  have hD (i j : I) := highSectionCovariantDerivative_zero_off d
    (fun z => (mu z*a z i j) • U z) S hS (hV i j) (axis i)
  have hDD (i j : I) := oneSectionCovariantDerivative_zero_off d
    (fun y => highSectionCovariantDerivative d (fun z => (mu z*a z i j) • U z) y (axis i))
    S hS (hD i j) (axis j) x hx
  simp only [scalarCovariantSecondTransposeSection,hDD,Finset.sum_const_zero,smul_zero]

theorem contDiff_supported_scalarCovariantSecondSection {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (a : MetricField) (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) :
    ContDiff ℝ ∞ (scalarCovariantSecondSection d a U) ∧
      ∀ x ∉ S,scalarCovariantSecondSection d a U x=0 := by
  have hD (j : I) := contDiff_supported_highSectionCovariantDerivative hY d hg hK he U hU S hS hSY h0 (axis j)
  have hDD (i j : I) := contDiff_supported_oneSectionCovariantDerivative hY d hg hK he
    (fun y => highSectionCovariantDerivative d U y (axis j)) (hD j).1 S hS hSY (hD j).2 (axis i)
  have hT (i j : I) : ContDiff ℝ ∞ (fun x => a x i j • oneSectionCovariantDerivative d
      (fun y => highSectionCovariantDerivative d U y (axis j)) x (axis i)) :=
    contDiff_supported_smul _ _ S hS (hDD i j).1 (hDD i j).2
      (fun x hx => (ha i j).contDiffAt (hY.mem_nhds (hSY hx)))
  exact ⟨ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => hT i j)),
    scalarCovariantSecondSection_zero_off d a U S hS h0⟩

/-- The genuine double transpose preserves the same supported smooth
core. This uses its checked defect identity on Y and exact exterior zeros. -/
theorem contDiff_supported_scalarCovariantSecondTransposeSection {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (mu : X → ℝ) (hmu : ContDiffOn ℝ ∞ mu Y) (hpos : ∀ x ∈ Y,mu x ≠ 0)
    (a : MetricField) (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (hSym : ∀ x ∈ Y,(a x).IsHermitian)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) :
    ContDiff ℝ ∞ (scalarCovariantSecondTransposeSection d mu a U) ∧
      ∀ x ∉ S,scalarCovariantSecondTransposeSection d mu a U x=0 := by
  have hSS := contDiff_supported_scalarCovariantSecondSection hY d hg hK he a ha U hU S hS hSY h0
  have hDS := contDiff_supported_scalarCovariantAdjointDefectSection hY d hg hK he mu hmu hpos a ha U hU S hS hSY h0
  have hEq : scalarCovariantSecondTransposeSection d mu a U=
      (fun x => scalarCovariantSecondSection d a U x+scalarCovariantAdjointDefectSection d mu a U x) := by
    funext x
    by_cases hx : x ∈ S
    · exact scalarCovariantSecondTransposeSection_eq_add_defect hY d hg hK he mu hmu a ha hSym U hU.contDiffOn
        (hSY hx) (hpos x (hSY hx))
    · rw [scalarCovariantSecondTransposeSection_zero_off d mu a U S hS h0 x hx,
        hSS.2 x hx,hDS.2 x hx,add_zero]
  refine ⟨?_,scalarCovariantSecondTransposeSection_zero_off d mu a U S hS h0⟩
  rw [hEq]
  exact hSS.1.add hDS.1

end ShrinkingSpheres
