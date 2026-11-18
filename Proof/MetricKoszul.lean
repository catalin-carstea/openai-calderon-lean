import Proof.GradientDivergence
import Proof.IndexedPolynomialHessian

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
namespace ShrinkingSpheres

lemma fderiv_metricPair_fixed {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) {x : X} (hx : x ∈ Ω) (a b c : X) :
    fderiv ℝ (fun y => metricPair g y b c) x a = metricDifferential g x a b c := by
  have hh := metric_pair_fderiv hΩ hg hx (fun _ => b) (fun _ => c)
    (differentiableAt_const _) (differentiableAt_const _) a
  simp only [fderiv_const_apply,zero_apply] at hh
  have h0L : metricPair g x 0 c = 0 := by simp [metricPair]
  have h0R : metricPair g x b 0 = 0 := by simp [metricPair]
  simpa only [h0L,h0R,add_zero] using hh

/-- Koszul's identity for the actual frozen Christoffel connection. -/
lemma Elliptic.metricKoszul {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (a b c : X) :
    2*metricPair g x (connection g x a b) c =
      metricDifferential g x a b c+metricDifferential g x b a c-metricDifferential g x c a b := by
  have h1 := connection_metric hΩ hg hK hx a b c
  have h2 := connection_metric hΩ hg hK hx b a c
  have h3 := connection_metric hΩ hg hK hx c a b
  rw [connection_symmetric hΩ hg hx b a] at h2
  rw [connection_symmetric hΩ hg hx c a,connection_symmetric hΩ hg hx c b] at h3
  rw [metricPair_symm g x b (connection g x a c) (hg.2 x hx).1] at h1
  linarith only [h1,h2,h3]

lemma metricPair_left_ext (g : MetricField) (e : Frame) (y : X)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (u v : X) (hPair : ∀ w : X,metricPair g y u w = metricPair g y v w) : u = v := by
  apply (frameBasis g e y hFrame).repr.injective
  apply Finsupp.ext
  intro i
  rw [frameBasis_repr,frameBasis_repr]
  exact hPair (e y i)

end ShrinkingSpheres
