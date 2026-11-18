import Proof.MovingTraceDriftField
import Proof.HorizontalFiberBounds
import Proof.ScaledFrozenAdjointFiber

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

theorem fiberSq_scaled_trace_sum_bound (e : Frame) (y : X) (r : ℝ) (c : I → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hc : ∀ i,|c i| ≤ K) (H A : I → X → ℂ)
    (hH : ∀ i,Continuous (fun w : UnitSphere => H i (frameVector e y w.val)))
    (hA : ∀ i,Continuous (fun w : UnitSphere => A i (frameVector e y w.val))) :
    fiberSq e y (fun w => r • ∑ i : I,c i • (H i w+A i w)) ≤
      6*K^2*r^2*∑ i : I,fiberSq e y (H i)+6*K^2*∑ i : I,fiberSq e y (fun w => r • A i w) := by
  let FH := fun w => r • ∑ i : I,c i • H i w
  let FA := fun w => ∑ i : I,c i • (r • A i w)
  have hSplit : (fun w => r • ∑ i : I,c i • (H i w+A i w)) = (fun w => FH w+FA w) := by
    funext w
    simp only [FH,FA,smul_add,Finset.sum_add_distrib,Finset.smul_sum,smul_smul,mul_comm]
  have hFH : Continuous (fun w : UnitSphere => FH (frameVector e y w.val)) :=
    (continuous_finsetSum _ (fun i _ => (hH i).const_smul (c i))).const_smul r
  have hFA : Continuous (fun w : UnitSphere => FA (frameVector e y w.val)) :=
    continuous_finsetSum _ (fun i _ => ((hA i).const_smul r).const_smul (c i))
  have hHBound : fiberSq e y FH ≤ 3*K^2*r^2*∑ i : I,fiberSq e y (H i) := by
    change fiberSq e y (fun w => r • ∑ i : I,c i • H i w) ≤ _
    rw [fiberSq_smul_real]
    exact (mul_le_mul_of_nonneg_left (fiberSq_real_weight_sum_three_le e y H hH c K hK hc)
      (sq_nonneg r)).trans_eq (by ring)
  have hABound : fiberSq e y FA ≤ 3*K^2*∑ i : I,fiberSq e y (fun w => r • A i w) :=
    fiberSq_real_weight_sum_three_le e y _ (fun i => (hA i).const_smul r) c K hK hc
  rw [hSplit]
  exact (fiberSq_add_le e y FH FA hFH hFA).trans
    ((add_le_add (mul_le_mul_of_nonneg_left hHBound (by norm_num : (0:ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hABound (by norm_num : (0:ℝ) ≤ 2))).trans_eq (by ring))

/-- The entire actual second-metric drift is controlled using only its
    admitted pointwise size and the actual scaled frozen-adjoint estimate. -/
theorem uniform_movingTraceDrift_fiber_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CA : ℝ,0 < η ∧ 0 ≤ CA ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ φ : Field,smoothNear φ (bundle Y d.γ) →
      fiberSq d.frame y (fun w => movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ (y,w)) ≤
        54*K^4*(d.radius y)^2*(∑ i : I,fiberSq d.frame y (fun w => horizontal d.γ φ y w (d.frame y i)))+
          18*K^2*CA^2*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w)) := by
  have hTheorem := uniform_scaled_frozen_adjoint_fiber hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CA,hη,hCA,hProduce⟩ := hTheorem
  refine ⟨η,CA,hη,hCA,?_⟩
  intro floor hf ε hε hSmall d hd y hy φ hφ
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hSub : Y ⊆ Ω := fun z hz => hd.2.1.center_mem hz
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun z hz => hd.1.1.2 z (hSub hz)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun z => d.frame z i) Y := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ z ∈ Y,∀ i j,metricPair d.γ z (d.frame z i) (d.frame z j) = if i=j then 1 else 0 :=
    fun z hz => hd.1.2.2.2.2.2.2.2 z (hSub hz)
  have hHCont (i : I) : Continuous (fun w : UnitSphere => horizontal d.γ φ y (frameVector d.frame y w.val) (axis i)) :=
    (smoothNear_horizontalField hY h hKpos (fun _ i => axis i) (fun _ => contDiffOn_const) hφ i).continuous_frame_fiber hy d.frame (hFrame y hy)
  have hACont (i : I) : Continuous (fun w : UnitSphere => adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) :=
    (hd.2.2.2.1 i φ hφ).1.continuous_frame_fiber hy d.frame (hFrame y hy)
  have hDrift (i : I) : |drift d.γ d.g₂ y i| ≤ K := hd.1.2.2.2.2.2.1 y (hSub hy) i
  have hBox := fiberSq_scaled_trace_sum_bound d.frame y (d.radius y) (drift d.γ d.g₂ y) K hKpos.le hDrift
    (fun i w => horizontal d.γ φ y w (axis i)) (fun i w => adjointField d.adjoint i φ (y,w)) hHCont hACont
  have hHSum := horizontal_coordinate_fiber_sum_bound hY h hK d.frame he hFrame hφ hy
  have hASum : (∑ i : I,fiberSq d.frame y (fun w => d.radius y • adjointField d.adjoint i φ (y,w))) ≤
      3*CA^2*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w)) := by
    simp only [fiberSq_smul_real]
    have hEach (i : I) := hProduce floor hf ε hε hSmall d hd y hy i φ hφ
    exact (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hEach i)).trans_eq
      (by rw [Fin.sum_univ_three];ring)
  have hCombined := add_le_add
    (mul_le_mul_of_nonneg_left hHSum (show 0 ≤ 6*K^2*(d.radius y)^2 by positivity))
    (mul_le_mul_of_nonneg_left hASum (show 0 ≤ 6*K^2 by positivity))
  exact hBox.trans (hCombined.trans_eq (by ring))

end ShrinkingSpheres
