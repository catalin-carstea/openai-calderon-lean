import Proof.FrameBasis
import Proof.MovingTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma zero_mem_disk (g : MetricField) (y : X) (s : ℝ) : (0:X) ∈ disk g y s := by
  change metricPair g y 0 0 ≤ s^2
  simpa [metricPair] using sq_nonneg s

lemma NormalCoordinates.exp_zero {Y Ω : Set X} {g : MetricField} {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) : expMap (y,0) = y := by
  have hz := (hN.2 y hy).2.2 0 (zero_mem_disk g y (R y))
  simpa only [zero_smul] using hz.2.2.1

lemma NormalCoordinates.differentiableAt_zero {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) :
    DifferentiableAt ℝ expMap (y,0) := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  exact (hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,zero_mem_disk g y (R y)⟩))).differentiableAt (by simp)

lemma NormalCoordinates.vertical_zero_on_disk {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) :
    fderiv ℝ expMap (y,0) (0,v) = v := by
  have hpath : HasDerivAt (fun t : ℝ => expMap (y,t • v))
      (fderiv ℝ expMap (y,0) (0,v)) 0 := by
    have hscale := (hasDerivAt_const (0:ℝ) y).prodMk ((hasDerivAt_id (0:ℝ)).smul_const v)
    have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,0)) (y,(0:ℝ) • v) := by
      simpa only [zero_smul] using (hN.differentiableAt_zero hy).hasFDerivAt
    convert hE.comp_hasDerivAt 0 hscale using 1 <;> simp only [Function.id_def,one_smul,Function.comp_def]
  exact hpath.deriv.symm.trans ((hN.2 y hy).2.2 v hv).2.2.2.1

/-- The zero-radius vertical Jacobian is the identity for every admitted normal map.
    The orthonormal frame is used only as a basis at this one center. -/
theorem NormalCoordinates.vertical_zero {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (v : X) :
    fderiv ℝ expMap (y,0) (0,v) = v := by
  have hR : R y ≠ 0 := (hN.2 y hy).1.ne'
  have hdir (i : I) : fderiv ℝ expMap (y,0) (0,e y i) = e y i := by
    have hi : e y i ∈ sphereAt g y := by change metricPair g y (e y i) (e y i) = 1; simpa using hframe i i
    have heq := hN.vertical_zero_on_disk hy (R y • e y i) (scaled_unit_mem_disk g y (e y i) (R y) hi)
    have hscaled : ((0:X),R y • e y i) = R y • ((0:X),e y i) := by simp
    rw [hscaled,map_smul] at heq
    have hh := congrArg (fun w : X => (R y)⁻¹ • w) heq
    simpa only [smul_smul,inv_mul_cancel₀ hR,one_smul] using hh
  let L : X →L[ℝ] X := (fderiv ℝ expMap (y,0)).comp (ContinuousLinearMap.inr ℝ X X)
  have hL : L.toLinearMap = (ContinuousLinearMap.id ℝ X).toLinearMap := by
    apply (frameBasis g e y hframe).ext
    intro i
    simpa only [L,ContinuousLinearMap.coe_comp,Function.comp_apply,ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.coe_coe,ContinuousLinearMap.id_apply,frameBasis_apply] using hdir i
  exact congrArg (fun F : X →ₗ[ℝ] X => F v) hL

/-- The full first jet at radius zero follows from the geodesic initial velocity and
    the identity exp_y(0)=y, without choosing a replacement exponential map. -/
theorem NormalCoordinates.hasFDerivAt_zero {Y Ω : Set X} (hY : IsOpen Y) {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    HasFDerivAt expMap (ContinuousLinearMap.fst ℝ X X+ContinuousLinearMap.snd ℝ X X) (y,0) := by
  have hE := hN.differentiableAt_zero hy
  have hbase : (fun z : X => expMap (z,0)) =ᶠ[𝓝 y] (fun z => z) :=
    (hY.eventually_mem hy).mono (fun z hz => hN.exp_zero hz)
  have hi : HasFDerivAt (fun z : X => (z,(0:X)))
      ((ContinuousLinearMap.id ℝ X).prod 0) y :=
    (hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const (𝕜:=ℝ) (0:X) y)
  have hd := hE.hasFDerivAt.comp y hi
  have hB (a : X) : fderiv ℝ expMap (y,0) (a,0) = a := by
    have hh := congrArg (fun F : X →L[ℝ] X => F a) (hd.fderiv.symm.trans hbase.fderiv_eq)
    simpa using hh
  convert hE.hasFDerivAt using 1
  apply ContinuousLinearMap.ext
  rintro ⟨a,b⟩
  have hab : (a,b) = ((a,0):X × X)+(0,b) := by simp
  change a+b = fderiv ℝ expMap (y,0) (a,b)
  rw [hab,map_add,hB,hN.vertical_zero hy e hframe b]

end ShrinkingSpheres
