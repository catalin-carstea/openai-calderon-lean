import Proof.FramedNormalMetric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma contDiff_frameVector_fixed (e : Frame) (y : X) : ContDiff ℝ ∞ (frameVector e y) := by
  convert (frameVectorLinear e y).contDiff using 1
  funext w
  exact (frameVectorLinear_apply e y w).symm

lemma contDiffAt_framedNormalMetric_entry (g : MetricField) (e : Frame) (expMap : X × X → X)
    (y z : X) (r : ℝ) (i j : I)
    (hExp : ContDiffAt ℝ ∞ expMap (y,r • frameVector e y z))
    (hMetric : ∀ a b,ContDiffAt ℝ ∞ (fun x => g x a b) (expMap (y,r • frameVector e y z))) :
    ContDiffAt ℝ ∞ (fun w => framedNormalMetric g e expMap y r w i j) z := by
  have hInput : ContDiffAt ℝ ∞ (fun w : X => (y,r • frameVector e y w)) z :=
    contDiffAt_const.prodMk ((contDiff_frameVector_fixed e y).contDiffAt.const_smul r)
  have hEnd : ContDiffAt ℝ ∞ (fun w : X => expMap (y,r • frameVector e y w)) z := hExp.comp z hInput
  have hJ (a : I) : ContDiffAt ℝ ∞ (fun w : X => fderiv ℝ expMap (y,r • frameVector e y w) (0,e y a)) z :=
    ((hExp.fderiv_right (m:=∞) (by simp)).comp z hInput).clm_apply contDiffAt_const
  have hCoord (a b : I) : ContDiffAt ℝ ∞ (fun w : X => (fderiv ℝ expMap (y,r • frameVector e y w) (0,e y a)) b) z :=
    (EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.contDiffAt.comp z (hJ a)
  have hG (a b : I) : ContDiffAt ℝ ∞ (fun w : X => g (expMap (y,r • frameVector e y w)) a b) z := by
    simpa only [Function.comp_def] using (hMetric a b).comp z hEnd
  change ContDiffAt ℝ ∞ (fun w : X => ∑ a,∑ b,g (expMap (y,r • frameVector e y w)) a b*
    (fderiv ℝ expMap (y,r • frameVector e y w) (0,e y i)) a*
    (fderiv ℝ expMap (y,r • frameVector e y w) (0,e y j)) b) z
  exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
    ((hG a b).mul (hCoord i a)).mul (hCoord j b)))

lemma framedNormalMetric_symmetric (g : MetricField) (e : Frame) (expMap : X × X → X)
    (y z : X) (r : ℝ) (hsym : (g (expMap (y,r • frameVector e y z))).transpose = g (expMap (y,r • frameVector e y z))) :
    (framedNormalMetric g e expMap y r z).transpose = framedNormalMetric g e expMap y r z := by
  ext i j
  change metricPair g (expMap (y,r • frameVector e y z))
    (fderiv ℝ expMap (y,r • frameVector e y z) (0,e y j))
    (fderiv ℝ expMap (y,r • frameVector e y z) (0,e y i)) = _
  exact metricPair_symm g _ _ _ hsym

/-- Smoothness of the actual pulled-back metric on the entire fixed closed unit ball. -/
theorem Admissible.contDiffAt_framedNormalMetric_entry {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) {g : MetricField}
    (hg : Elliptic Ω K g) (z : X) (hz : z ∈ Metric.closedBall (0:X) 1) (i j : I) :
    ContDiffAt ℝ ∞ (fun w => framedNormalMetric g d.frame d.expMap y (d.radius y) w i j) z := by
  have hframe := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hw := frameVector_mem_unitDisk d.γ d.frame y z hframe hz
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hwd := scaled_unitDisk_mem_disk d.γ y (frameVector d.frame y z) (d.radius y) hw
  have hv : d.radius y • frameVector d.frame y z ∈ disk d.γ y (max ρ (d.radius y)) :=
    hwd.trans ((sq_le_sq₀ hr.le (hr.le.trans (le_max_right ..))).2 (le_max_right ..))
  obtain ⟨U,hU,hTube,hReg⟩ := hd.2.1.1
  have hExp : ContDiffAt ℝ ∞ d.expMap (y,d.radius y • frameVector d.frame y z) :=
    hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))
  have hx := hd.endpoint_unitDisk_mem hy _ hw
  exact ShrinkingSpheres.contDiffAt_framedNormalMetric_entry g d.frame d.expMap y z (d.radius y) i j hExp
    (fun a b => (hg.1 a b).contDiffAt (hΩ.mem_nhds hx))

end ShrinkingSpheres
