import Proof.PullbackMatrixPointEllipticity
import Proof.NormalJacobianInverse
import Proof.TauEllipticityBridge
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped Matrix.Norms.Elementwise
namespace ShrinkingSpheres
lemma NormalCoordinates.normalFrameMetric_posDef_of_orthonormal {Y Ω : Set X}
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (L : X →L[ℝ] X) (r : ℝ) (z : X)
    (he : ∀ i j,metricPair g y (L (axis i)) (L (axis j))=if i=j then 1 else 0)
    (hv : r • L z ∈ disk g y (R y)) :
    (normalFrameMetric g E ((y,(r,L)),z)).PosDef := by
  let J := normalVerticalJacobian E y (r • L z)
  let x := E (y,r • L z)
  have hx : x ∈ Ω := by
    simpa only [x,one_smul] using hN.path_image hy (r • L z) hv (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
  have hJ : Function.Injective J := (hN.normalVerticalJacobian_isInvertible hy _ hv).injective
  have hL : Function.Injective L := by
    intro u v huv
    have hZero : L (u-v)=0 := by rw [map_sub,huv,sub_self]
    have hPair := metricPair_orthonormal_linear g (y,(0,L)) he (u-v) (u-v)
    rw [hZero] at hPair
    have hh : inner ℝ (u-v) (u-v)=0 := by
      simpa only [metricPair,PiLp.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero] using hPair.symm
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hh)
  rw [normalFrameMetric_eq_universal_pullback]
  change (universalPullbackMetricMatrix (g x,(J,L))).PosDef
  have hSym : (universalPullbackMetricMatrix (g x,(J,L))).IsSymm := by
    ext i j
    exact metricPair_symm g x _ _ (hg.2 x hx).1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hSym) ?_
  intro v hv0
  let u : X := WithLp.toLp 2 v
  have hu : u ≠ 0 := by
    intro hu0
    exact hv0 (congrArg WithLp.ofLp hu0)
  have hJu : J (L u) ≠ 0 := by
    intro hz
    apply hu
    apply hL
    apply hJ
    simpa only [map_zero] using hz
  have hp : 0 < metricPair g x (J (L u)) (J (L u)) :=
    (mul_pos (inv_pos.mpr hK) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hJu))).trans_le
      ((hg.2 x hx).2 (J (L u))).1
  have hPair : metricPair (fun _ => universalPullbackMetricMatrix (g x,(J,L))) 0 u u=
      metricPair g x (J (L u)) (J (L u)) := universalPullbackMetricMatrix_pair (g x) J L u u
  have hpPull : 0 < metricPair (fun _ => universalPullbackMetricMatrix (g x,(J,L))) 0 u u := hPair.symm ▸ hp
  simpa only [star_trivial,dotProduct_mulVec_eq_metricPair] using
    ((dotProduct_mulVec_eq_metricPair (fun _ => universalPullbackMetricMatrix (g x,(J,L))) 0 u u).symm ▸ hpPull)
end ShrinkingSpheres
