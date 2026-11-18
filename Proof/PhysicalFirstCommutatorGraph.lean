import Proof.PhysicalFirstCommutatorMeasurability
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma AngularComponentData.horizontalHalfSection_covariant {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L) (hY : IsOpen Y) {K : ℝ}
    (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) (i : I) :
    Q.horizontalHalfSection i y=halfSectionCovariantDerivativeL d
      (ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth)) y (d.frame y i) :=
  (Q.half_covariant_section_eq hY hg hK he hFrame hφ hy i).symm

/-- The estimated form is the actual full-first mixed commutator on the
same physical horizontal fields, evaluated on a genuine common core. -/
lemma PhysicalFirstCommutatorPacket.form_graph {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} (W : PhysicalFirstCommutatorPacket P CB CS ε)
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L) {y : X} (hy : y ∈ Y) :
    firstCommutatorForm (fun i j => W.commLow i j y) (fun i => Q.horizontalHalfSection i y)=
      ∑ i : I,∑ j : I,sphereSobolevDualPairing (1/2:ℝ) (Q.horizontalHalfSection i y)
        ((P.firstDerivativeHalfL y i).adjoint
          (P.firstDerivativeHigherL y j (Q.horizontalThreeHalfSection j y))-
          P.firstDerivativeHalfL y j (W.adjointHigh i y (Q.horizontalThreeHalfSection j y))) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := DFunLike.congr_fun (W.comm_graph i j y hy) (Q.horizontalThreeHalfSection j y)
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,Q.horizontalThreeHalfSection_inclusion] at h
  exact congrArg (fun z => sphereSobolevDualPairing (1/2:ℝ) (Q.horizontalHalfSection i y) z) h.symm
end ShrinkingSpheres
