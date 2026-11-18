import Proof.FramedNormalRegularity
import Proof.EnlargedNormalInverse
import Proof.EnlargedFramedEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 20
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Joint center/angular regularity of the actual framed normal metric.
    This is a statement about the genuine map, without choosing coefficient representatives. -/
lemma contDiffAt_framedNormalMetric_joint_entry
    (g : MetricField) (e : Frame) (expMap : X × X → X) (r : X → ℝ) (y z : X) (i j : I)
    (he : ∀ a,ContDiffAt ℝ ∞ (fun x => e x a) y) (hr : ContDiffAt ℝ ∞ r y)
    (hExp : ContDiffAt ℝ ∞ expMap (y,r y • frameVector e y z))
    (hMetric : ∀ a b,ContDiffAt ℝ ∞ (fun x => g x a b) (expMap (y,r y • frameVector e y z))) :
    ContDiffAt ℝ ∞ (fun p : X × X => framedNormalMetric g e expMap p.1 (r p.1) p.2 i j) (y,z) := by
  have hFrame (a : I) : ContDiffAt ℝ ∞ (fun p : X × X => e p.1 a) (y,z) :=
    (he a).comp (y,z) contDiffAt_fst
  have hCoord (a : I) : ContDiffAt ℝ ∞ (fun p : X × X => p.2 a) (y,z) :=
    (EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.contDiffAt.comp (y,z) contDiffAt_snd
  have hW : ContDiffAt ℝ ∞ (fun p : X × X => frameVector e p.1 p.2) (y,z) :=
    ContDiffAt.sum (fun a _ => (hCoord a).smul (hFrame a))
  have hInput : ContDiffAt ℝ ∞ (fun p : X × X => (p.1,r p.1 • frameVector e p.1 p.2)) (y,z) :=
    contDiffAt_fst.prodMk ((hr.comp (y,z) contDiffAt_fst).smul hW)
  have hEnd : ContDiffAt ℝ ∞ (fun p : X × X => expMap (p.1,r p.1 • frameVector e p.1 p.2)) (y,z) :=
    hExp.comp (y,z) hInput
  have hJ (a : I) : ContDiffAt ℝ ∞ (fun p : X × X =>
      fderiv ℝ expMap (p.1,r p.1 • frameVector e p.1 p.2) (0,e p.1 a)) (y,z) :=
    ((hExp.fderiv_right (m:=∞) (by simp)).comp (y,z) hInput).clm_apply
      (contDiffAt_const.prodMk (hFrame a))
  have hJacCoord (a b : I) : ContDiffAt ℝ ∞ (fun p : X × X =>
      (fderiv ℝ expMap (p.1,r p.1 • frameVector e p.1 p.2) (0,e p.1 a)) b) (y,z) :=
    (EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.contDiffAt.comp (y,z) (hJ a)
  have hG (a b : I) : ContDiffAt ℝ ∞ (fun p : X × X =>
      g (expMap (p.1,r p.1 • frameVector e p.1 p.2)) a b) (y,z) := by
    simpa only [Function.comp_def] using (hMetric a b).comp (y,z) hEnd
  change ContDiffAt ℝ ∞ (fun p : X × X => ∑ a,∑ b,
    g (expMap (p.1,r p.1 • frameVector e p.1 p.2)) a b*
    (fderiv ℝ expMap (p.1,r p.1 • frameVector e p.1 p.2) (0,e p.1 i)) a*
    (fderiv ℝ expMap (p.1,r p.1 • frameVector e p.1 p.2) (0,e p.1 j)) b) (y,z)
  exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
    ((hG a b).mul (hJacCoord i a)).mul (hJacCoord j b)))

/-- One common threshold gives true joint smoothness for every admitted
    reference/first metric on each enlarged normal ball. -/
theorem uniform_framed_normal_metric_joint_regular {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      ContDiffAt ℝ ∞ (fun p : X × X => framedNormalMetric g d.frame d.expMap p.1
        (d.radius p.1) p.2 i j) (y,z) := by
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem z hz i j
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hw := frameVector_mem_disk d.γ d.frame y z L hFrame hz
  have hPack := hControl floor hf ε hε hSmall d hd y hy (frameVector d.frame y z) hw
  have hEll : Elliptic Ω K g := by
    have hh := hmem
    simp only [mem_insert_iff,mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact hd.1.1
    · exact hd.1.2.1
  exact contDiffAt_framedNormalMetric_joint_entry g d.frame d.expMap d.radius y z i j
    (fun a => (hd.1.2.2.2.2.2.2.1 a).contDiffAt (hΩ.mem_nhds hCenter))
    (hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)) hPack.2.2.1
    (fun a b => (hEll.1 a b).contDiffAt (hΩ.mem_nhds hPack.2.1))

end ShrinkingSpheres
