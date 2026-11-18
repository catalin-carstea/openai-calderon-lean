import Proof.UniversalPullbackMatrixJets
import Proof.EnlargedFramedEllipticity
import Proof.NormalFrameNormalizationGerms
import Proof.BackgroundMetricSprayInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

lemma universalPullbackMetricMatrix_pair (A : Mat) (J L : X →L[ℝ] X) (u v : X) :
    metricPair (fun _ => universalPullbackMetricMatrix (A,(J,L))) 0 u v =
      metricPair (fun _ => A) 0 (J (L u)) (J (L v)) := by
  have hSlot (w : X) : J (L w) = ∑ i,w i • J (L (axis i)) := by
    calc
      J (L w) = J (frameVector (fun _ i => L (axis i)) 0 w) :=
        congrArg J (frameVector_linear_axes L 0 w).symm
      _ = _ := by simp only [frameVector,map_sum,map_smul]
  change (∑ i,∑ j,universalPullbackMetricMatrix (A,(J,L)) i j*u i*v j) = _
  rw [hSlot u,hSlot v,metricPair_sum_left]
  simp_rw [metricPair_smul_left,metricPair_sum_right,metricPair_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (∑ a,∑ b,A a b*(J (L (axis i))) a*(J (L (axis j))) b)*u i*v j =
    u i*(v j*(∑ a,∑ b,A a b*(J (L (axis i))) a*(J (L (axis j))) b))
  ring

/-- A pointwise orthonormal frame and a Jacobian within one half of identity
    give a uniformly elliptic constant metric matrix. -/
theorem Elliptic.universalPullbackMetricMatrix_elliptic {Ω : Set X} {K : ℝ} {g a : MetricField}
    (hg : Elliptic Ω K g) (ha : Elliptic Ω K a) (hK : 0 < K)
    (y x : X) (hy : y ∈ Ω) (hx : x ∈ Ω) (J L : X →L[ℝ] X)
    (he : ∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0)
    (hJ : ‖J-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ)) :
    Elliptic (Set.univ:Set X) (4*K^2) (fun _ => universalPullbackMetricMatrix (a x,(J,L))) := by
  let G := universalPullbackMetricMatrix (a x,(J,L))
  have hPair (u v : X) : metricPair (fun _ => G) 0 u v = metricPair a x (J (L u)) (J (L v)) :=
    universalPullbackMetricMatrix_pair (a x) J L u v
  have hSym : G.transpose = G := by
    ext i j
    change metricPair a x (J (L (axis j))) (J (L (axis i))) =
      metricPair a x (J (L (axis i))) (J (L (axis j)))
    exact metricPair_symm a x _ _ (ha.2 x hx).1
  refine ⟨fun _ _ => contDiffOn_const,fun z _ => ⟨hSym,?_⟩⟩
  intro u
  have hFrame := hg.frameVector_norm_sq_bounds hK hy (fun _ i => L (axis i)) he u
  simp only [frameVector_linear_axes] at hFrame
  have hb := metricPair_pullback_bounds ha hK hx J hJ (L u)
  have hConst : 0 < 4*K^2 := by positivity
  have hLo : ‖u‖^2 ≤ (4*K^2)*metricPair a x (J (L u)) (J (L u)) := by
    have hh := hFrame.1.trans (mul_le_mul_of_nonneg_left hb.1 hK.le)
    convert hh using 1 <;> ring
  have hHi : metricPair a x (J (L u)) (J (L u)) ≤ (4*K^2)*‖u‖^2 := by
    have hh := hb.2.trans (mul_le_mul_of_nonneg_left hFrame.2 (show 0 ≤ 4*K by positivity))
    convert hh using 1 <;> ring
  change (4*K^2)⁻¹*‖u‖^2 ≤ metricPair (fun _ => G) 0 u u ∧
    metricPair (fun _ => G) 0 u u ≤ (4*K^2)*‖u‖^2
  rw [hPair]
  refine ⟨?_,hHi⟩
  have hh := mul_le_mul_of_nonneg_left hLo (inv_nonneg.mpr hConst.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ hConst.ne',one_mul] using hh

theorem Elliptic.universalPullbackMetricMatrix_point_bounds {Ω : Set X} {K : ℝ} {g a : MetricField}
    (hg : Elliptic Ω K g) (ha : Elliptic Ω K a) (hK : 0 < K)
    (y x : X) (hy : y ∈ Ω) (hx : x ∈ Ω) (J L : X →L[ℝ] X)
    (he : ∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0)
    (hJ : ‖J-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ)) :
    ‖universalPullbackMetricMatrix (a x,(J,L))‖ ≤ 4*K^2 ∧
      (((metricDensityBudget (4*K^2))⁻¹)^2) ≤ (universalPullbackMetricMatrix (a x,(J,L))).det := by
  have h := hg.universalPullbackMetricMatrix_elliptic ha hK y x hy hx J L he hJ
  have hKp : 0 < 4*K^2 := by positivity
  have hPos := (h.posDef hKp (mem_univ (0:X))).det_pos
  refine ⟨(Matrix.norm_le_iff hKp.le).mpr (fun i j => h.entry_abs_bound hKp (mem_univ (0:X)) i j),?_⟩
  have hh := h.det_lower_bound_of_density hKp (mem_univ (0:X))
  simpa only [abs_of_pos hPos] using hh

end ShrinkingSpheres
