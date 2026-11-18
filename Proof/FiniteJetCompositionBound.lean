import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma norm_iteratedFDeriv_comp_at_bound (f : E → F) (g : F → G) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (n : ℕ) (C D : ℝ)
    (hC : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (n.factorial : ℝ)*C*D^n := by
  obtain ⟨t,ht,hxt,hgtRaw⟩ := hg.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  have hgt : ContDiffOn ℝ (n : ℕ∞ω) g t := by simpa using hgtRaw
  obtain ⟨u,hu,hxu,hfuRaw⟩ := hf.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  have hfu : ContDiffOn ℝ (n : ℕ∞ω) f u := by simpa using hfuRaw
  have hpre : f ⁻¹' t ∈ 𝓝 x := hf.continuousAt.preimage_mem_nhds (ht.mem_nhds hxt)
  obtain ⟨v,hv,hvopen,hxv⟩ := _root_.mem_nhds_iff.mp hpre
  let s := u ∩ v
  have hs : IsOpen s := hu.inter hvopen
  have hx : x ∈ s := ⟨hxu,hxv⟩
  have hfs : ContDiffOn ℝ (n : ℕ∞ω) f s := hfu.mono inter_subset_left
  have hst : MapsTo f s t := fun y hy => hv hy.2
  have hcg (i : ℕ) : iteratedFDerivWithin ℝ i g t (f x) = iteratedFDeriv ℝ i g (f x) :=
    iteratedFDerivWithin_eq_iteratedFDeriv ht.uniqueDiffOn (hg.of_le (by simp)) hxt
  have hcf (i : ℕ) : iteratedFDerivWithin ℝ i f s x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hf.of_le (by simp)) hx
  have hcomp := hg.comp x hf
  have hccomp : iteratedFDerivWithin ℝ n (g ∘ f) s x = iteratedFDeriv ℝ n (g ∘ f) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hcomp.of_le (by simp)) hx
  have hN : (n : ℕ∞ω) ≤ (n : ℕ∞ω) := le_rfl
  have h := norm_iteratedFDerivWithin_comp_le hgt hfs hN ht.uniqueDiffOn hs.uniqueDiffOn
    hst hx (fun i hi => by rw [hcg]; exact hC i hi)
    (fun i hi hin => by rw [hcf]; exact hD i hi hin)
  rwa [hccomp] at h

 

end ShrinkingSpheres
