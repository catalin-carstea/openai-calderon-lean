import Proof.NormalJacobianSecondDerivative
import Proof.NormalMetricCloseness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma metricDifferential_abs_le (g : MetricField) (x : X) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ i j,‖fderiv ℝ (fun z => g z i j) x‖ ≤ M) (a u w : X) :
    |metricDifferential g x a u w| ≤ 9*M*‖a‖*‖u‖*‖w‖ := by
  have hTerm (i j : I) : |fderiv ℝ (fun z => g z i j) x a*u i*w j| ≤ M*‖a‖*‖u‖*‖w‖ := by
    have hda : |fderiv ℝ (fun z => g z i j) x a| ≤ M*‖a‖ := by
      simpa only [Real.norm_eq_abs] using ((fderiv ℝ (fun z => g z i j) x).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hD i j) (norm_nonneg a))
    have hui : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    have hwj : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w j
    rw [abs_mul,abs_mul]
    gcongr
  rw [metricDifferential_apply]
  calc
    _ ≤ ∑ i,∑ j,|fderiv ℝ (fun z => g z i j) x a*u i*w j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : I,∑ _j : I,M*‖a‖*‖u‖*‖w‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma metric_pair_comp_differentiableAt {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (F U V : X → X) (x : X) (hx : F x ∈ Ω)
    (hF : DifferentiableAt ℝ F x) (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) :
    DifferentiableAt ℝ (fun z => metricPair g (F z) (U z) (V z)) x := by
  have hG (i j : I) := (((h.1 i j).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).comp x hF
  have hUi (i : I) := (EuclideanSpace.proj (𝕜:=ℝ) i).differentiableAt.comp x hU
  have hVj (j : I) := (EuclideanSpace.proj (𝕜:=ℝ) j).differentiableAt.comp x hV
  change DifferentiableAt ℝ (fun z => ∑ i,∑ j,g (F z) i j*(U z) i*(V z) j) x
  exact DifferentiableAt.fun_sum (fun i _ => DifferentiableAt.fun_sum
    (fun j _ => ((hG i j).mul (hUi i)).mul (hVj j)))

lemma metric_pair_comp_fderiv {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (F U V : X → X) (x : X) (hx : F x ∈ Ω)
    (hF : DifferentiableAt ℝ F x) (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) (a : X) :
    fderiv ℝ (fun z => metricPair g (F z) (U z) (V z)) x a =
      metricDifferential g (F x) (fderiv ℝ F x a) (U x) (V x)+
        metricPair g (F x) (fderiv ℝ U x a) (V x)+metricPair g (F x) (U x) (fderiv ℝ V x a) := by
  have hG (i j : I) := ((((h.1 i j).contDiffAt (hΩ.mem_nhds hx)).differentiableAt
    (by simp)).hasFDerivAt).comp x hF.hasFDerivAt
  have hU' (i : I) := (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt.comp x hU.hasFDerivAt
  have hV' (i : I) := (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt.comp x hV.hasFDerivAt
  have hsum := HasFDerivAt.sum (u:=Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u:=Finset.univ) (fun j _ => ((hG i j).mul (hU' i)).mul (hV' j)))
  have hfun : (fun z => metricPair g (F z) (U z) (V z)) =
      ∑ i,∑ j,((fun z => g z i j) ∘ F)*((EuclideanSpace.proj i) ∘ U)*((EuclideanSpace.proj j) ∘ V) := by
    funext z
    simp [metricPair,PiLp.proj_apply]
  rw [hfun,hsum.fderiv]
  simp only [_root_.sum_apply,ContinuousLinearMap.add_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,Function.comp_apply,Pi.mul_apply,PiLp.proj_apply,
    smul_eq_mul,metricDifferential_apply,metricPair]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma NormalCoordinates.hasFDerivAt_velocity_slice {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) :
    HasFDerivAt (fun x => expMap (y,x)) (normalVerticalJacobian expMap y v) v := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,v)) (y,v) :=
    ((hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))).differentiableAt (by simp)).hasFDerivAt
  have hInput : HasFDerivAt (fun x : X => (y,x)) (ContinuousLinearMap.inr ℝ X X) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  exact hE.comp v hInput

/-- Differentiate the actual unscaled normal metric in a velocity direction. -/
lemma NormalCoordinates.normal_metric_velocity_derivative {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {γ g : MetricField} (hg : Elliptic Ω K g)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y)
    (v u w a : X) (hv : v ∈ disk γ y (R y)) :
    fderiv ℝ (fun z => metricPair g (expMap (y,z))
        (normalVerticalJacobian expMap y z u) (normalVerticalJacobian expMap y z w)) v a =
      metricDifferential g (expMap (y,v)) (normalVerticalJacobian expMap y v a)
        (normalVerticalJacobian expMap y v u) (normalVerticalJacobian expMap y v w)+
      metricPair g (expMap (y,v)) (fderiv ℝ (normalVerticalJacobian expMap y) v a u)
        (normalVerticalJacobian expMap y v w)+
      metricPair g (expMap (y,v)) (normalVerticalJacobian expMap y v u)
        (fderiv ℝ (normalVerticalJacobian expMap y) v a w) := by
  have hF := hN.hasFDerivAt_velocity_slice hy v hv
  have hJ := (hN.contDiffAt_normalVerticalJacobian hy v hv).differentiableAt (by simp)
  have hU := hJ.hasFDerivAt.clm_apply (hasFDerivAt_const u v)
  have hW := hJ.hasFDerivAt.clm_apply (hasFDerivAt_const w v)
  have hPos := ((hN.2 y hy).2.2 v hv).1
  have hh := metric_pair_comp_fderiv hΩ hg (fun z => expMap (y,z))
    (fun z => normalVerticalJacobian expMap y z u) (fun z => normalVerticalJacobian expMap y z w)
    v hPos hF.differentiableAt hU.differentiableAt hW.differentiableAt a
  rw [hF.fderiv,hU.fderiv,hW.fderiv] at hh
  simpa only [_root_.add_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,zero_add] using hh

/-- Norm bound for the velocity derivative of the actual normal pullback metric. -/
theorem NormalCoordinates.normal_metric_velocity_derivative_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K M J₀ J₁ : ℝ} {γ g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hM : 0 ≤ M) (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y)
    (v u w a : X) (hv : v ∈ disk γ y (R y))
    (hD : ∀ i j,‖fderiv ℝ (fun z => g z i j) (expMap (y,v))‖ ≤ M)
    (hJ : ‖normalVerticalJacobian expMap y v‖ ≤ J₀)
    (hDJ : ‖fderiv ℝ (normalVerticalJacobian expMap y) v‖ ≤ J₁) :
    |fderiv ℝ (fun z => metricPair g (expMap (y,z))
        (normalVerticalJacobian expMap y z u) (normalVerticalJacobian expMap y z w)) v a| ≤
      (9*M*J₀^3+2*K*J₀*J₁)*‖a‖*‖u‖*‖w‖ := by
  let J := normalVerticalJacobian expMap y v
  let DJ := fderiv ℝ (normalVerticalJacobian expMap y) v
  have hPos := ((hN.2 y hy).2.2 v hv).1
  have hJn (b : X) : ‖J b‖ ≤ J₀*‖b‖ :=
    (J.le_opNorm b).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg b))
  have hDJn (b c : X) : ‖DJ b c‖ ≤ J₁*‖b‖*‖c‖ :=
    (norm_bilinear_apply_le DJ b c).trans (by gcongr)
  have hOne : |metricDifferential g (expMap (y,v)) (J a) (J u) (J w)| ≤
      (9*M*J₀^3)*‖a‖*‖u‖*‖w‖ := by
    have hh := metricDifferential_abs_le g (expMap (y,v)) M hM hD (J a) (J u) (J w)
    have hb : |metricDifferential g (expMap (y,v)) (J a) (J u) (J w)| ≤
        9*M*(J₀*‖a‖)*(J₀*‖u‖)*(J₀*‖w‖) := hh.trans (by gcongr; exact hJn a; exact hJn u; exact hJn w)
    exact hb.trans_eq (by ring)
  have hTwo : |metricPair g (expMap (y,v)) (DJ a u) (J w)| ≤
      (K*J₀*J₁)*‖a‖*‖u‖*‖w‖ := by
    have hh := hg.metricPair_abs_le hK hPos (DJ a u) (J w)
    have hb : |metricPair g (expMap (y,v)) (DJ a u) (J w)| ≤
        K*(J₁*‖a‖*‖u‖)*(J₀*‖w‖) := hh.trans (by gcongr; exact hDJn a u; exact hJn w)
    exact hb.trans_eq (by ring)
  have hThree : |metricPair g (expMap (y,v)) (J u) (DJ a w)| ≤
      (K*J₀*J₁)*‖a‖*‖u‖*‖w‖ := by
    have hh := hg.metricPair_abs_le hK hPos (J u) (DJ a w)
    have hb : |metricPair g (expMap (y,v)) (J u) (DJ a w)| ≤
        K*(J₀*‖u‖)*(J₁*‖a‖*‖w‖) := hh.trans (by gcongr; exact hJn u; exact hDJn a w)
    exact hb.trans_eq (by ring)
  rw [hN.normal_metric_velocity_derivative hΩ hg hy v u w a hv]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (by linarith only [hOne,hTwo,hThree])

end ShrinkingSpheres
