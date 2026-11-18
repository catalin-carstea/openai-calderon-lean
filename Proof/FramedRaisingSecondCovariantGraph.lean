import Proof.FramedRaisingCovariantGraph
import Proof.FramedRaisingHalfEndpoints
import Proof.CovariantRotationGraphOperations
import Proof.MetricConnection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def framedRaisingFirstCoarseJet (d : Data) (i b : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ a : I,christoffel d.γ x a i b • framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a)

lemma framedRaisingFirstCoarseJet_eq (d : Data) (i b : I) (x : X) :
    framedRaisingFirstCoarseJet d i b x =
      framedFlatRaisingSobolevL 1 d.γ d.frame x (connection d.γ x (axis i) (axis b)) := by
  rw [framedFlatRaisingSobolevL_axis_expansion]
  simp only [framedRaisingFirstCoarseJet,connection_axis_components]

def framedRaisingSecondCoarseJet (d : Data) (i j b : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ a : I,
    (christoffel d.γ x a i b •
        framedFlatRaisingSobolevL 1 d.γ d.frame x (connection d.γ x (axis j) (axis a))+
      fderiv ℝ (fun y => christoffel d.γ y a i b) x (axis j) •
        framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a))

lemma Admissible.framedRaisingFirstCoarseJet_smooth {Y Ω : Set X}
    (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (i b : I) :
    ContDiffOn ℝ ∞ (framedRaisingFirstCoarseJet d i b) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  exact ContDiffOn.sum (fun a _ =>
    ((hd.1.1.contDiffOn_christoffel hΩ hK a i b).mono hSub).smul
      (hd.framedRaisingHalf_smooth (axis a)).2.2)

lemma Admissible.framedRaising_first_second_covariant_graphs {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (i j b : I) :
    CoarseCovariantRotationGraph d y (axis i)
      (fun x => framedFlatRaisingSobolevL 1 d.γ d.frame x (axis b)) (framedRaisingFirstCoarseJet d i b y) ∧
    CoarseCovariantRotationGraph d y (axis j) (framedRaisingFirstCoarseJet d i b)
      (framedRaisingSecondCoarseJet d i j b y) := by
  have hyΩ := hd.2.1.center_mem hy
  have hR (a : I) := framedFlatRaising_covariant_graph hΩ d hd.1.1 hK
    hd.1.2.2.2.2.2.2.1 hd.1.2.2.2.2.2.2.2 hyΩ (axis j) (axis a)
  constructor
  · rw [framedRaisingFirstCoarseJet_eq]
    exact framedFlatRaising_covariant_graph hΩ d hd.1.1 hK
      hd.1.2.2.2.2.2.2.1 hd.1.2.2.2.2.2.2.2 hyΩ (axis i) (axis b)
  · exact CoarseCovariantRotationGraph.sum_three
      (fun a x => christoffel d.γ x a i b • framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a))
      (fun a => christoffel d.γ y a i b •
        framedFlatRaisingSobolevL 1 d.γ d.frame y (connection d.γ y (axis j) (axis a))+
        fderiv ℝ (fun x => christoffel d.γ x a i b) y (axis j) •
          framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a))
      (fun a => (hR a).smul (fun x => christoffel d.γ x a i b)
        (((hd.1.1.contDiffOn_christoffel hΩ hK a i b).contDiffAt (hΩ.mem_nhds hyΩ)).differentiableAt (by simp))
        ((((hd.framedRaisingHalf_smooth (axis a)).2.2).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
      (fun a => ((((hd.1.1.contDiffOn_christoffel hΩ hK a i b).mono
        (fun x hx => hd.2.1.center_mem hx)).smul (hd.framedRaisingHalf_smooth (axis a)).2.2).contDiffAt
          (hY.mem_nhds hy)).differentiableAt (by simp))

end ShrinkingSpheres
