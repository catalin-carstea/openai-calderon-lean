import Proof.RelativeNormalizationHorizontalTangent
import Proof.NormalizedRelativeAngularCurve
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def relativeRightRotationL (i j : I) :
    NormalFrameRelativeParameter →L[ℝ] NormalFrameRelativeParameter :=
  (ContinuousLinearMap.inl ℝ (X × (X →L[ℝ] X)) ℝ).comp
    ((ContinuousLinearMap.inr ℝ X (X →L[ℝ] X)).comp
      (((ContinuousLinearMap.compL ℝ X X X).flip (rotationVectorL i j)).comp
        relativeFrameProjectionL))

lemma relativeRightRotationL_apply (i j : I) (p : NormalFrameRelativeParameter) :
    relativeRightRotationL i j p = ((0,p.1.2.comp (rotationVectorL i j)),0) := rfl

/-- Right angular variation commutes with the ambient-direction horizontal
lift. The connection and logarithmic-radius covector only depend on the
center, which is fixed by this angular variation. -/
lemma horizontal_field_angular_affine (g : MetricField) (r : X → ℝ)
    (a : X) (p : NormalFrameRelativeParameter) (i j : I) (t : ℝ) :
    normalFrameRelativeHorizontalField g r a (p+t • relativeRightRotationL i j p) =
      normalFrameRelativeHorizontalField g r a p+
        t • relativeRightRotationL i j (normalFrameRelativeHorizontalField g r a p) := by
  rw [relativeRightRotationL_apply,relativeRightRotationL_apply]
  apply Prod.ext
  · apply Prod.ext
    · change a = a+t • (0:X)
      simp only [smul_zero,add_zero]
    · change -((connectionBilinear g (p.1.1+t • (0:X)) a).comp
          (p.1.2+t • p.1.2.comp (rotationVectorL i j))) =
        -((connectionBilinear g p.1.1 a).comp p.1.2)+
          t • (-((connectionBilinear g p.1.1 a).comp p.1.2)).comp (rotationVectorL i j)
      simp only [smul_zero,add_zero,ContinuousLinearMap.comp_add,
        ContinuousLinearMap.comp_smul,neg_add_rev,ContinuousLinearMap.neg_comp,
        smul_neg,ContinuousLinearMap.comp_assoc]
      abel
  · change (1+(p.2+t*(0:ℝ)))*
        fderiv ℝ (fun x => Real.log (r x)) (p.1.1+t • (0:X)) a =
      (1+p.2)*fderiv ℝ (fun x => Real.log (r x)) p.1.1 a+t*(0:ℝ)
    simp only [mul_zero,add_zero,smul_zero]

lemma fderiv_horizontal_field_angular (g : MetricField) (r : X → ℝ)
    (a : X) (p : NormalFrameRelativeParameter) (i j : I)
    (hX : DifferentiableAt ℝ (normalFrameRelativeHorizontalField g r a) p) :
    fderiv ℝ (normalFrameRelativeHorizontalField g r a) p (relativeRightRotationL i j p) =
      relativeRightRotationL i j (normalFrameRelativeHorizontalField g r a p) := by
  have hLine := (hasDerivAt_const (0:ℝ) p).add
    ((hasDerivAt_id (0:ℝ)).smul_const (relativeRightRotationL i j p))
  change HasDerivAt (fun t : ℝ => p+t • relativeRightRotationL i j p) _ 0 at hLine
  simp only [one_smul,zero_add] at hLine
  have hAt : HasFDerivAt (normalFrameRelativeHorizontalField g r a)
      (fderiv ℝ (normalFrameRelativeHorizontalField g r a) p)
      (p+(0:ℝ) • relativeRightRotationL i j p) := by
    simpa only [zero_smul,add_zero] using hX.hasFDerivAt
  have hD := hAt.comp_hasDerivAt 0 hLine
  change HasDerivAt (fun t : ℝ => normalFrameRelativeHorizontalField g r a
    (p+t • relativeRightRotationL i j p)) _ 0 at hD
  simp_rw [horizontal_field_angular_affine] at hD
  have hAffine := (hasDerivAt_const (0:ℝ) (normalFrameRelativeHorizontalField g r a p)).add
    ((hasDerivAt_id (0:ℝ)).smul_const
      (relativeRightRotationL i j (normalFrameRelativeHorizontalField g r a p)))
  change HasDerivAt (fun t : ℝ => normalFrameRelativeHorizontalField g r a p+
    t • relativeRightRotationL i j (normalFrameRelativeHorizontalField g r a p)) _ 0 at hAffine
  simp only [one_smul,zero_add] at hAffine
  exact hD.unique hAffine

private lemma normalized_generator_horizontal_commutation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : E → E) (J : E →L[ℝ] E) (V : E → E) (f : E → F) (p : E)
    (hN : DifferentiableAt ℝ N p) (hNp : N p=p)
    (hNV : fderiv ℝ N p (V p)=V p)
    (hV : DifferentiableAt ℝ V p) (hJV : fderiv ℝ V p (J p)=J (V p))
    (hf : ContDiffAt ℝ ∞ f p) :
    fderiv ℝ (fun q => fderiv ℝ f (N q) (J (N q))) p (V p) =
      fderiv ℝ (fun q => fderiv ℝ f q (V q)) p (J p) := by
  have hDf := (hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hDfN : DifferentiableAt ℝ (fun q => fderiv ℝ f (N q)) p := by
    apply DifferentiableAt.comp p _ hN
    simpa only [hNp] using hDf
  have hJN : DifferentiableAt ℝ (fun q => J (N q)) p := J.differentiableAt.comp p hN
  rw [fderiv_clm_apply hDfN hJN,fderiv_clm_apply hDf hV]
  have hDComp : fderiv ℝ (fun q => fderiv ℝ f (N q)) p =
      (fderiv ℝ (fderiv ℝ f) p).comp (fderiv ℝ N p) := by
    have hAt : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p) (N p) := by
      simpa only [hNp] using hDf.hasFDerivAt
    exact (hAt.comp p hN.hasFDerivAt).fderiv
  have hJComp : fderiv ℝ (fun q => J (N q)) p = J.comp (fderiv ℝ N p) :=
    (J.hasFDerivAt.comp p hN.hasFDerivAt).fderiv
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    hDComp,hJComp,hNp,hNV,hJV]
  congr 1
  exact (hf.isSymmSndFDerivAt (by simp)) (V p) (J p)

/-- Horizontal differentiation commutes with the normalized angular
generator on an orthonormal parameter, with no frame-derivative estimate. -/
theorem fderiv_relative_angular_horizontal_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (r : X → ℝ)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ i j, metricPair g p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j)) =
      if i=j then 1 else 0) (a : X) (i j : I)
    (F : NormalFrameRelativeParameter → E) (hF : ContDiffAt ℝ ∞ F p)
    (hX : DifferentiableAt ℝ (normalFrameRelativeHorizontalField g r a) p) :
    fderiv ℝ (normalFrameRelativeAngularDerivative g F i j) p
        (normalFrameRelativeHorizontalField g r a p) =
      normalFrameRelativeAngularDerivative g
        (fun q => fderiv ℝ F q (normalFrameRelativeHorizontalField g r a q)) i j p := by
  have hN := ((h.contDiffOn_normalFrameRelativeNormalization hΩ hK).contDiffAt
    ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hp)).differentiableAt (by simp)
  have hNp := normalFrameRelativeNormalization_eq_self g p he
  have hComm := normalized_generator_horizontal_commutation
    (normalFrameRelativeNormalization g) (relativeRightRotationL i j)
    (normalFrameRelativeHorizontalField g r a) F p hN hNp
    (fderiv_relativeNormalization_horizontal hΩ h hK r p hp he a) hX
    (fderiv_horizontal_field_angular g r a p i j hX) hF
  change fderiv ℝ (fun q => fderiv ℝ F (normalFrameRelativeNormalization g q)
    (relativeRightRotationL i j (normalFrameRelativeNormalization g q))) p _ = _ at hComm
  change fderiv ℝ (fun q => fderiv ℝ F (normalFrameRelativeNormalization g q)
    (relativeRightRotationL i j (normalFrameRelativeNormalization g q))) p _ = _
  rw [hComm]
  unfold normalFrameRelativeAngularDerivative normalFrameRelativeAngularTangent
  rw [hNp]
  rfl

end ShrinkingSpheres
