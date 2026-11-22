module

public import Proof.Manuscript.MovingTrace.StereographicPolarCollar
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open Set Filter Classical
open scoped ContDiff Topology

namespace CalderonPaper

variable {P A Z F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Transfer a compactly supported collar function to the full ambient
ball, with the same geometry parameters. -/
def collarLift (e : OpenPartialHomeomorph A Z) (v : P × A → F) (q : P × Z) : F :=
  if q.2 ∈ e.target then v (q.1,e.symm q.2) else 0

theorem collarLift_readout (e : OpenPartialHomeomorph A Z) (v : P × A → F)
    {p : P} {x : A} (hx : x ∈ e.source) : collarLift e v (p,e x) = v (p,x) := by
  rw [collarLift,ite_eq_left (e.map_source hx), e.left_inv hx]

theorem collarLift_zero_off_image (e : OpenPartialHomeomorph A Z) (v : P × A → F)
    {K : Set A} (hSupp : ∀ p x, x ∉ K → v (p,x) = 0)
    (q : P × Z) (hq : q.2 ∉ e '' K) : collarLift e v q = 0 := by
  by_cases hIn : q.2 ∈ e.target
  · rw [collarLift,ite_eq_left hIn]
    exact hSupp q.1 _ (fun hMem => hq ⟨e.symm q.2,hMem,e.right_inv hIn⟩)
  · rw [collarLift,ite_eq_right hIn]

theorem tsupport_collarLift_subset (e : OpenPartialHomeomorph A Z) (v : P × A → F)
    {K : Set A} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (hSupp : ∀ p x, x ∉ K → v (p,x) = 0) (p : P) :
    tsupport (fun z => collarLift e v (p,z)) ⊆ e '' K := by
  have hClosed : IsClosed (e '' K) := (hK.image_of_continuousOn (e.continuousOn.mono hKe)).isClosed
  apply closure_minimal (fun z hz => ?_) hClosed
  by_contra hout
  exact hz (collarLift_zero_off_image e v hSupp (p,z) hout)

/-- Joint smoothness survives extension by zero whenever the entire
spatial support stays in a compact subregion of the collar chart. -/
theorem contDiff_collarLift (e : OpenPartialHomeomorph A Z)
    (he : ContDiffOn ℝ ∞ e.symm e.target) {v : P × A → F}
    (hv : ContDiffOn ℝ ∞ v (univ ×ˢ e.source))
    {K : Set A} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (hSupp : ∀ p x, x ∉ K → v (p,x) = 0) : ContDiff ℝ ∞ (collarLift e v) := by
  let V : Set (P × Z) := univ ×ˢ e.target
  have hV : IsOpen V := isOpen_univ.prod e.open_target
  have hClosed : IsClosed (e '' K) := (hK.image_of_continuousOn (e.continuousOn.mono hKe)).isClosed
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q.2 ∈ e.target
  · have hqV : q ∈ V := ⟨mem_univ _, hq⟩
    have hA : ContDiffOn ℝ ∞ (fun z : P × Z => (z.1,e.symm z.2)) V := by
      exact contDiffOn_fst.prodMk (he.comp contDiffOn_snd fun z hz => hz.2)
    have hMaps : MapsTo (fun z : P × Z => (z.1,e.symm z.2)) V (univ ×ˢ e.source) :=
      fun z hz => ⟨mem_univ _,e.map_target hz.2⟩
    apply ((hv.comp hA hMaps).contDiffAt (hV.mem_nhds hqV)).congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hqV] with z hz
    exact ite_eq_left hz.2
  · have hOut : IsOpen (univ ×ˢ (e '' K)ᶜ : Set (P × Z)) :=
      isOpen_univ.prod hClosed.isOpen_compl
    have hqOut : q ∈ (univ ×ˢ (e '' K)ᶜ : Set (P × Z)) := by
      refine ⟨mem_univ _,?_⟩
      rintro ⟨x,hx,hEx⟩
      exact hq (hEx ▸ e.map_source (hKe hx))
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : P × Z => (0:F)) q).congr_of_eventuallyEq
    filter_upwards [hOut.mem_nhds hqOut] with z hz
    exact collarLift_zero_off_image e v hSupp z hz.2

end CalderonPaper
