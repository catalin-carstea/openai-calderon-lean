import Proof.UniformFramedEllipticity
import Proof.EnlargedFramedEllipticity
import Proof.Archive.CollaboratorFixedDirichletRegularityOct17

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set Matrix
namespace ShrinkingSpheres

lemma dotProduct_mulVec_eq_metricPair (g : MetricField) (x u v : X) :
    u.ofLp ⬝ᵥ ((g x) *ᵥ v.ofLp) = metricPair g x u v := by
  simp only [dotProduct,Matrix.mulVec,metricPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma Elliptic.metricPair_cauchy_sq {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (u v : X) :
    (metricPair g x u v)^2 ≤ metricPair g x u u*metricPair g x v v := by
  have hh := (hg.posDef hK hx).star_dotProduct_mulVec_mul_le u.ofLp v.ofLp
  simpa only [star_trivial,dotProduct_mulVec_eq_metricPair,← pow_two] using hh

/-- The symmetric quadratic ellipticity interface controls the entire bilinear form,
    with the same constant, in the exact probability-sphere tangent coordinates. -/
lemma Elliptic.metricPair_abs_le {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (u v : X) :
    |metricPair g x u v| ≤ K*‖u‖*‖v‖ := by
  have hc := hg.metricPair_cauchy_sq hK hx u v
  have hU := ((hg.2 x hx).2 u).2
  have hV := ((hg.2 x hx).2 v).2
  have hV0 : 0 ≤ metricPair g x v v :=
    (mul_nonneg (inv_nonneg.mpr hK.le) (sq_nonneg ‖v‖)).trans ((hg.2 x hx).2 v).1
  have hp := mul_le_mul hU hV hV0 (mul_nonneg hK.le (sq_nonneg ‖u‖))
  apply (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ K*‖u‖*‖v‖ by positivity)).mp
  have hh := hc.trans hp
  convert hh using 1 <;> (try simp only [sq_abs]) <;> ring

/-- The actual geometric ellipticity bounds imply Tau Ceti's divergence-form
    ellipticity predicate, with no unproved PDE or coefficient premise. -/
theorem Elliptic.to_tau_uniformlyEllipticOn {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 1 ≤ K) :
    TauCeti.PDE.UniformlyEllipticOn Ω g K⁻¹ K := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨inv_pos.mpr hKpos,?_,?_⟩
  · have hh : (1:ℝ) ≤ K*K := by nlinarith
    have hMul := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hKpos.le)
    simpa only [mul_one,← mul_assoc,inv_mul_cancel₀ hKpos.ne',one_mul] using hMul
  · intro x hx
    constructor
    · intro u
      simpa only [Matrix.toQuadraticForm'_apply,dotProduct_mulVec_eq_metricPair] using ((hg.2 x hx).2 u).1
    · intro u v
      simpa only [dotProduct_mulVec_eq_metricPair] using hg.metricPair_abs_le hKpos hx u v

end ShrinkingSpheres
