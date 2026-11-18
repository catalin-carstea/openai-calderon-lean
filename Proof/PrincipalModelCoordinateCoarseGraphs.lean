import Proof.PrincipalModelCoordinateCoarse
import Proof.CoarseCovariantSecondProduct
import Proof.DegreeCovariantGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Both actual covariant graphs for the SAME complete model coordinate
coefficient, including degree and physical raising parts. -/
theorem Admissible.principalModelCoordinate_coarse_covariant_graphs {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (b i j : I) :
    CoarseCovariantRotationGraph d y (axis i) (principalModelCoordinateCoarseL d b)
      (principalModelCoordinateFirstCoarseJet d b i y) ∧
    CoarseCovariantRotationGraph d y (axis j) (principalModelCoordinateFirstCoarseJet d b i)
      (principalModelCoordinateSecondCoarseJet d b i j y) := by
  have hW := hd.contDiffOn_principalModelDegreeCoordinateWeight hY hK b
  have hWD := contDiffOn_coordDeriv hY hW i
  have hWR (a : I) := hd.contDiffOn_principalModelRaisingCoordinateWeight hK a b
  have hWRD (a : I) := contDiffOn_coordDeriv hY (hWR a) i
  have hR (a : I) := (hd.framedRaisingHalf_smooth (axis a)).2.2
  have hS (a : I) := hd.framedRaisingFirstCoarseJet_smooth hΩ hK i a
  have hTerm (a : I) : ContDiffOn ℝ ∞ (fun x =>
      principalModelRaisingCoordinateWeight d a b x • framedRaisingFirstCoarseJet d i a x+
        fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i) •
          framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a)) Y :=
    ((hWR a).smul (hS a)).add ((hWRD a).smul (hR a))
  have hRGraphs (a k l : I) := hd.framedRaising_first_second_covariant_graphs hY hΩ hK hy k l a
  have hDG : CoarseCovariantRotationGraph d y (axis i)
      (fun x => principalModelDegreeCoordinateWeight d b x • sphereSobolevDegreeL)
      (fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i) • sphereSobolevDegreeL) := by
    simpa only [smul_zero,zero_add] using (sphereSobolevDegreeL_covariant_graph d y (axis i)).smul
      (principalModelDegreeCoordinateWeight d b) ((hW.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (differentiableAt_const _)
  have hRG := CoarseCovariantRotationGraph.sum_three
    (fun a x => principalModelRaisingCoordinateWeight d a b x • framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a))
    (fun a => principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstCoarseJet d i a y+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a))
    (fun a => ((hRGraphs a i i).1).smul (principalModelRaisingCoordinateWeight d a b)
      (((hWR a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hR a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
    (fun a => (((hWR a).smul (hR a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  constructor
  · exact hDG.add hRG
      (((hW.smul contDiffOn_const).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((ContDiffOn.sum (fun a _ => (hWR a).smul (hR a))).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  · have hDDG : CoarseCovariantRotationGraph d y (axis j)
        (fun x => fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i) • sphereSobolevDegreeL)
        (fderiv ℝ (fun x => fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i)) y (axis j) •
          sphereSobolevDegreeL) := by
      simpa only [smul_zero,zero_add] using (sphereSobolevDegreeL_covariant_graph d y (axis j)).smul
        (fun x => fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i))
        ((hWD.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) (differentiableAt_const _)
    have hRRG := CoarseCovariantRotationGraph.sum_three
      (fun a x => principalModelRaisingCoordinateWeight d a b x • framedRaisingFirstCoarseJet d i a x+
        fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i) •
          framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a))
      (fun a => (principalModelRaisingCoordinateWeight d a b y • framedRaisingSecondCoarseJet d i j a y+
        fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis j) • framedRaisingFirstCoarseJet d i a y)+
        (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingFirstCoarseJet d j a y+
          fderiv ℝ (fun x => fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i)) y (axis j) •
            framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)))
      (fun a => coarse_covariant_second_weighted_graph (b:=axis i) (c:=axis j)
        (principalModelRaisingCoordinateWeight d a b)
        (fun x => framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a))
        (framedRaisingFirstCoarseJet d i a) (framedRaisingFirstCoarseJet d j a y)
        (framedRaisingSecondCoarseJet d i j a y)
        ((hWR a).contDiffAt (hY.mem_nhds hy))
        (((hR a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hS a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (hRGraphs a j j).1 (hRGraphs a i j).2)
      (fun a => ((hTerm a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    exact hDDG.add hRRG
      (((hWD.smul contDiffOn_const).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((ContDiffOn.sum (fun a _ => hTerm a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))

end ShrinkingSpheres
