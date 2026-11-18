import Proof.PhysicalTraceRegularity
import Proof.NormalGeodesicBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma smoothNear.smul_base {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    {f : X → ℝ} (hf : ContDiffOn ℝ ∞ f Y) {φ : Field}
    (hφ : smoothNear φ (bundle Y g)) :
    smoothNear (fun p : X × X => f p.1 • φ p) (bundle Y g) := by
  obtain ⟨V,hV,hb,hφV⟩ := hφ
  refine ⟨V ∩ Prod.fst ⁻¹' Y,hV.inter (hY.preimage continuous_fst),
    fun p hp => ⟨hb hp,hp.1⟩,?_⟩
  exact (hf.comp contDiffOn_fst (fun p hp => hp.2)).smul (hφV.mono inter_subset_left)

lemma sphereAverage_sub_of_continuous (e : Frame) (y : X) (F G : X → ℂ)
    (hF : Continuous (fun v : UnitSphere => F (frameVector e y v.val)))
    (hG : Continuous (fun v : UnitSphere => G (frameVector e y v.val))) :
    sphereAverage e y (fun w => F w-G w) = sphereAverage e y F-sphereAverage e y G := by
  exact integral_sub (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

lemma sphere_pairing_eq {Y : Set X} {g : MetricField} {e : Frame} {y : X}
    {F G : Field} (hF : smoothNear F (bundle Y g)) (hG : smoothNear G (bundle Y g))
    (hy : y ∈ Y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hpair : ∀ a : X → ℝ,smoothNear a (sphereAt g y) →
      sphereAverage e y (fun w => F (y,w)*(a w : ℂ)) =
        sphereAverage e y (fun w => G (y,w)*(a w : ℂ))) :
    ∀ w ∈ sphereAt g y,F (y,w)=G (y,w) := by
  have hDiff : smoothNear (fun p => F p-G p) (bundle Y g) := by
    simpa only [sub_eq_add_neg] using hF.add hG.neg
  have hZero := sphere_pairing_separates (hDiff.sphere_slice hy) hframe (by
    intro a ha
    have hca : Continuous (fun v : UnitSphere => (a (frameVector e y v.val) : ℂ)) := by
      obtain ⟨V,hV,hb,haV⟩ := ha
      apply Complex.continuous_ofReal.comp
      exact haV.continuousOn.comp_continuous
        ((frameVectorLinear e y).continuous.comp continuous_subtype_val)
        (fun v => hb (frameVector_mem_sphere g e y hframe v))
    have hEq := sphereAverage_sub_of_continuous e y
      (fun w => F (y,w)*(a w : ℂ)) (fun w => G (y,w)*(a w : ℂ))
      (((hF.sphere_slice hy).continuous_frame_slice hframe).mul hca)
      (((hG.sphere_slice hy).continuous_frame_slice hframe).mul hca)
    simp only [sub_mul]
    rw [hEq,hpair a ha,sub_self])
  intro w hw
  exact sub_eq_zero.mp (hZero w hw)

theorem IsMovingTraceAdjoint.eq_on_sphere_of_duality
    {Y : Set X} {g g₁ : MetricField} {e : Frame} {expMap : X × X → X}
    {r : X → ℝ} {A : TraceAdjoint}
    (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A)
    (hD : Dirichlet Y g g₁ expMap r)
    {φ F : Field} (hφ : smoothNear φ (bundle Y g)) (hF : smoothNear F (bundle Y g))
    (i : I) {y : X} (hy : y ∈ Y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hdual : ∀ u : X → ℝ,HarmonicOnBall g₁ (closedBallImage g expMap r y) u →
      sphereAverage e y (fun w => F (y,w)*(u (endpoint expMap r (y,w)) : ℂ)) =
        sphereAverage e y (fun w => φ (y,w)*
          (horizontal g (fun p => u (endpoint expMap r p)) y w (axis i) : ℝ))) :
    ∀ w ∈ sphereAt g y,adjointField A i φ (y,w)=F (y,w) := by
  apply sphere_pairing_eq (hA i φ hφ).1 hF hy hframe
  intro a ha
  obtain ⟨u,hu,_⟩ := hD y hy a ha
  have hBoundary (H : Field) : sphereAverage e y (fun w => H (y,w)*(a w : ℂ)) =
      sphereAverage e y (fun w => H (y,w)*(u (endpoint expMap r (y,w)) : ℂ)) := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro v
    exact congrArg (fun t : ℝ => H (y,frameVector e y v.val)*(t : ℂ))
      (hu.2 _ (frameVector_mem_sphere g e y hframe v)).symm
  rw [hBoundary,hBoundary,(hA i φ hφ).2 y hy u hu.1,hdual u hu.1]

theorem IsMovingTraceAdjoint.base_smul
    {Y : Set X} (hY : IsOpen Y) {g g₁ : MetricField} {e : Frame}
    {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A)
    (hD : Dirichlet Y g g₁ expMap r) {f : X → ℝ} (hf : ContDiffOn ℝ ∞ f Y)
    {φ : Field} (hφ : smoothNear φ (bundle Y g))
    (i : I) {y : X} (hy : y ∈ Y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) :
    ∀ w ∈ sphereAt g y,adjointField A i (fun p => f p.1 • φ p) (y,w) =
      f y • adjointField A i φ (y,w) := by
  apply hA.eq_on_sphere_of_duality hD (hφ.smul_base hY hf)
    ((hA i φ hφ).1.smul_base hY hf) i hy hframe
  intro u hu
  have h := (hA i φ hφ).2 y hy u hu
  have hLeft : sphereAverage e y (fun w => (f y • adjointField A i φ (y,w))*
        (u (endpoint expMap r (y,w)) : ℂ)) =
      f y • sphereAverage e y (fun w => adjointField A i φ (y,w)*
        (u (endpoint expMap r (y,w)) : ℂ)) := by
    simp only [sphereAverage,smul_mul_assoc]
    exact MeasureTheory.integral_smul _ _
  have hRight : sphereAverage e y (fun w => (f y • φ (y,w))*
        (horizontal g (fun p => u (endpoint expMap r p)) y w (axis i) : ℝ)) =
      f y • sphereAverage e y (fun w => φ (y,w)*
        (horizontal g (fun p => u (endpoint expMap r p)) y w (axis i) : ℝ)) := by
    simp only [sphereAverage,smul_mul_assoc]
    exact MeasureTheory.integral_smul _ _
  exact hLeft.trans ((congrArg (fun z : ℂ => f y • z) h).trans hRight.symm)

theorem Admissible.contDiffAt_dirichlet_trace {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y w : X} (hy : y ∈ Y)
    (hw : w ∈ sphereAt d.γ y) (u : X → ℝ)
    (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u) :
    ContDiffAt ℝ ∞ (fun p => u (endpoint d.expMap d.radius p)) (y,w) := by
  have hrad := (hd.2.2.2.2.1.2 y hy).1
  have hwd := scaled_unit_mem_disk d.γ y w (d.radius y) hw
  have ht : d.radius y • w ∈ disk d.γ y (max ρ (d.radius y)) :=
    hwd.trans ((sq_le_sq₀ hrad.le (hrad.le.trans (le_max_right ..))).2 (le_max_right ..))
  obtain ⟨U,hU,hTube,hExp⟩ := hd.2.1.1
  obtain ⟨V,hV,hBall,hSol⟩ := hu.1
  have hE : ContDiffAt ℝ ∞ d.expMap (y,d.radius y • w) :=
    hExp.contDiffAt (hU.mem_nhds (hTube ⟨hy,ht⟩))
  have hS : ContDiffAt ℝ ∞ u (d.expMap (y,d.radius y • w)) :=
    hSol.contDiffAt (hV.mem_nhds (hBall ⟨d.radius y • w,hwd,rfl⟩))
  have hR : ContDiffAt ℝ ∞ d.radius y := hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)
  have hP : ContDiffAt ℝ ∞ (fun p : X × X => (p.1,d.radius p.1 • p.2)) (y,w) :=
    contDiffAt_fst.prodMk ((hR.comp (y,w) contDiffAt_fst).smul contDiffAt_snd)
  change ContDiffAt ℝ ∞ (u ∘ d.expMap ∘ (fun p : X × X => (p.1,d.radius p.1 • p.2))) (y,w)
  exact hS.comp (y,w) (hE.comp (y,w) hP)

theorem Admissible.continuous_dirichlet_horizontal {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (u : X → ℝ) (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u)
    (a : X) :
    Continuous (fun z : UnitSphere => horizontal d.γ (fun p => u (endpoint d.expMap d.radius p))
      y (frameVector d.frame y z.val) a) := by
  have hframe := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hV : Continuous (fun z : UnitSphere => frameVector d.frame y z.val) :=
    (frameVectorLinear d.frame y).continuous.comp continuous_subtype_val
  have hP : Continuous (fun z : UnitSphere => (y,frameVector d.frame y z.val)) :=
    continuous_const.prodMk hV
  have hC : Continuous (fun z : UnitSphere => (a,-connection d.γ y a (frameVector d.frame y z.val))) := by
    apply continuous_const.prodMk
    have hConn := ((connectionBilinear d.γ y a).continuous.comp hV).neg
    apply hConn.congr
    intro z
    exact congrArg Neg.neg (connectionBilinear_apply d.γ y a (frameVector d.frame y z.val))
  apply continuous_iff_continuousAt.mpr
  intro z
  have hT := hd.contDiffAt_dirichlet_trace hY hy (frameVector_mem_sphere d.γ d.frame y hframe z) u hu
  have hF := (hT.fderiv_right (m:=∞) (by simp)).continuousAt
  exact (hF.comp (f := fun z : UnitSphere => (y,frameVector d.frame y z.val))
    hP.continuousAt).clm_apply hC.continuousAt

theorem Admissible.adjoint_add {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {φ ψ : Field} (hφ : smoothNear φ (bundle Y d.γ)) (hψ : smoothNear ψ (bundle Y d.γ))
    (i : I) {y : X} (hy : y ∈ Y) :
    ∀ w ∈ sphereAt d.γ y,adjointField d.adjoint i (fun p => φ p+ψ p) (y,w) =
      adjointField d.adjoint i φ (y,w)+adjointField d.adjoint i ψ (y,w) := by
  have hA := hd.2.2.2.1
  have hframe := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hφA := (hA i φ hφ).1
  have hψA := (hA i ψ hψ).1
  apply hA.eq_on_sphere_of_duality hd.2.2.1 (hφ.add hψ) (hφA.add hψA) i hy hframe
  intro u hu
  have hTrace : Continuous (fun z : UnitSphere => (u (endpoint d.expMap d.radius (y,frameVector d.frame y z.val)) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hd.contDiffAt_dirichlet_trace hY hy
      (frameVector_mem_sphere d.γ d.frame y hframe z) u hu).continuousAt.comp
      (f := fun z : UnitSphere => (y,frameVector d.frame y z.val))
      (continuous_const.prodMk ((frameVectorLinear d.frame y).continuous.comp continuous_subtype_val)).continuousAt
  have hHor : Continuous (fun z : UnitSphere =>
      ((horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y
        (frameVector d.frame y z.val) (axis i) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hd.continuous_dirichlet_horizontal hY hy u hu (axis i))
  have hI (F : Field) (hF : smoothNear F (bundle Y d.γ)) (G : UnitSphere → ℂ) (hG : Continuous G) :
      Integrable (fun z : UnitSphere => F (y,frameVector d.frame y z.val)*G z) sphereProbability :=
    (((hF.sphere_slice hy).continuous_frame_slice hframe).mul hG).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLeft := integral_add (hI _ hφA _ hTrace) (hI _ hψA _ hTrace)
  have hRight := integral_add (hI _ hφ _ hHor) (hI _ hψ _ hHor)
  have hEq := congrArg₂ (fun a b : ℂ => a+b) ((hA i φ hφ).2 y hy u hu) ((hA i ψ hψ).2 y hy u hu)
  calc
    _ = sphereAverage d.frame y (fun w => adjointField d.adjoint i φ (y,w)*
          (u (endpoint d.expMap d.radius (y,w)) : ℂ)) +
        sphereAverage d.frame y (fun w => adjointField d.adjoint i ψ (y,w)*
          (u (endpoint d.expMap d.radius (y,w)) : ℂ)) := by
      simpa only [sphereAverage,frameVector,add_mul,Pi.add_apply,sphereProbability,surfaceMeasure,
        UnitSphere,standardSphere] using hLeft
    _ = _ := hEq
    _ = _ := by simpa only [sphereAverage,frameVector,add_mul,Pi.add_apply,sphereProbability,surfaceMeasure,
        UnitSphere,standardSphere] using hRight.symm

end ShrinkingSpheres
