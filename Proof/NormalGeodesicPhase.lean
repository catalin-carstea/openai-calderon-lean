import Proof.LocalFlowVariation
import Proof.NormalGeodesicBounds
import Proof.ConnectionOperatorBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def normalGeodesicPosition (expMap : X × X → X) (y : X) (p : X × ℝ) : X := expMap (y,p.2 • p.1)

def normalGeodesicPhase (expMap : X × X → X) (y : X) (p : X × ℝ) : X × X :=
  (normalGeodesicPosition expMap y p,fderiv ℝ (normalGeodesicPosition expMap y) p (0,1))

def coordinateGeodesicSpray (g : MetricField) (p : X × X) : X × X :=
  (p.2,-connection g p.1 p.2 p.2)

lemma NormalCoordinates.contDiffAt_position {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (p : X × ℝ) (hp : p.2 • p.1 ∈ disk g y (R y)) :
    ContDiffAt ℝ ∞ (normalGeodesicPosition expMap y) p := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,p.2 • p.1) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hp⟩))
  exact hE.comp p (contDiffAt_const.prodMk (contDiffAt_snd.smul contDiffAt_fst))

lemma NormalCoordinates.contDiffAt_phase {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (p : X × ℝ) (hp : p.2 • p.1 ∈ disk g y (R y)) :
    ContDiffAt ℝ ∞ (normalGeodesicPhase expMap y) p := by
  have hPos := hN.contDiffAt_position hy p hp
  exact hPos.prodMk ((hPos.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)

lemma NormalCoordinates.phase_eq {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    normalGeodesicPhase expMap y (v,t) =
      (expMap (y,t • v),deriv (fun s : ℝ => expMap (y,s • v)) t) := by
  have hPos := hN.contDiffAt_position hy (v,t) (smul_mem_disk_of_mem g y v (R y) t hv ht)
  have hd := (hasDerivAt_time_slice (normalGeodesicPosition expMap y) v t (hPos.differentiableAt (by simp))).deriv
  exact Prod.ext rfl hd.symm

/-- The actual normal-coordinate phase solves the coordinate spray equation, for
    every admitted initial velocity, without replacing it by a chosen global flow. -/
theorem NormalCoordinates.hasDerivAt_phase {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s : ℝ => normalGeodesicPhase expMap y (v,s))
      (coordinateGeodesicSpray g (normalGeodesicPhase expMap y (v,t))) t := by
  have hPos := hN.contDiffAt_position hy (v,t) (smul_mem_disk_of_mem g y v (R y) t hv ht)
  have hP := hasDerivAt_time_slice (normalGeodesicPosition expMap y) v t (hPos.differentiableAt (by simp))
  have hV := hasDerivAt_time_derivative (normalGeodesicPosition expMap y) v t hPos
  have hODE : deriv (deriv (fun s : ℝ => normalGeodesicPosition expMap y (v,s))) t =
      -connection g (normalGeodesicPosition expMap y (v,t))
        (deriv (fun s : ℝ => normalGeodesicPosition expMap y (v,s)) t)
        (deriv (fun s : ℝ => normalGeodesicPosition expMap y (v,s)) t) :=
    ((hN.2 y hy).2.2 v hv).2.2.2.2 t ht
  rw [hP.deriv] at hODE
  have hacc := (second_deriv_time_slice (normalGeodesicPosition expMap y) v t hPos).symm.trans hODE
  rw [hacc] at hV
  exact hP.prodMk hV

lemma NormalCoordinates.phase_zero {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) : normalGeodesicPhase expMap y (v,0) = (y,v) := by
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  rw [hN.phase_eq hy v hv hz]
  have hGeo := (hN.2 y hy).2.2 v hv
  exact Prod.ext hGeo.2.2.1 hGeo.2.2.2.1

lemma Elliptic.contDiffAt_coordinateGeodesicSpray {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) (p : X × X) (hp : p.1 ∈ Ω) :
    ContDiffAt ℝ ∞ (coordinateGeodesicSpray g) p := by
  have hΓ := (hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hp)
  have hconn := ((hΓ.comp p contDiffAt_fst).clm_apply contDiffAt_snd).clm_apply contDiffAt_snd
  convert contDiffAt_snd.prodMk hconn.neg using 1
  funext q
  simp only [coordinateGeodesicSpray,Function.comp_def,connectionBilinear_apply]

end ShrinkingSpheres
