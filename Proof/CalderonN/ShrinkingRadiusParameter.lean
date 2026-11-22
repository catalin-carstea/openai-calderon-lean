module

public import Proof.CalderonN.Radius
public import Proof.CalderonN.Chart

import Proof.CalderonN.NormalInverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ}

/-- The change from regularization parameter to sphere radius keeps the
center fixed. -/
@[expose] def shrinkingRadiusParameterMap (R : ℝ) (p : ℕ) (depth : (X dim) → ℝ)
    (q : ℝ × (X dim)) : ℝ × (X dim) := (shrinkingRadius R p depth q.1 q.2,q.2)

theorem contDiffOn_shrinkingRadius_parameter {Y : Set (X dim)} {depth : (X dim) → ℝ}
    (hd : ContDiffOn ℝ ∞ depth Y) (R : ℝ) (p : ℕ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => shrinkingRadius R p depth q.1 q.2)
      (Ioi (0 : ℝ) ×ˢ Y) := by
  let D := Ioi (0 : ℝ) ×ˢ Y
  have ht : ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => depth q.2) D :=
    hd.comp contDiff_snd.contDiffOn (fun _ hq => hq.2)
  have hdiv := ht.div contDiff_fst.contDiffOn (fun q (hq : q ∈ D) => hq.1.ne')
  have hsum : ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => 1 + Real.exp (depth q.2 / q.1)) D :=
    contDiffOn_const.add hdiv.exp
  have hs := hsum.log (fun _ _ => by positivity)
  exact contDiffOn_const.mul ((contDiff_fst.contDiffOn.mul hs).pow p)

/-- On the open positive parameter range, the actual radius family has a
jointly smooth inverse at every center. -/
theorem exists_inverse_shrinkingRadius_parameter
    {Y : Set (X dim)} (hY : IsOpen Y) {depth : (X dim) → ℝ} (hd : ContDiffOn ℝ ∞ depth Y)
    {R : ℝ} (hR : 0 < R) {p : ℕ} (hp : 0 < p) :
    let D := Ioi (0 : ℝ) ×ˢ Y
    let f := shrinkingRadiusParameterMap R p depth
    IsOpen (f '' D) ∧ ∃ v : (ℝ × (X dim)) → (ℝ × (X dim)),
      ContDiffOn ℝ ∞ v (f '' D) ∧ LeftInvOn v f D ∧ MapsTo v (f '' D) D ∧ RightInvOn v f (f '' D) := by
  let D := Ioi (0 : ℝ) ×ˢ Y
  let f := shrinkingRadiusParameterMap R p depth
  let h (q : ℝ × (X dim)) := shrinkingRadius R p depth q.1 q.2
  have ho : IsOpen D := isOpen_Ioi.prod hY
  have hh : ContDiffOn ℝ ∞ h D := contDiffOn_shrinkingRadius_parameter hd R p
  have hf : ContDiffOn ℝ ∞ f D := hh.prodMk contDiff_snd.contDiffOn
  have hinj : InjOn f D := by
    rintro ⟨a,y⟩ ⟨ha,hy⟩ ⟨b,z⟩ ⟨hb,hz⟩ he
    have he' : y = z := congrArg Prod.snd he
    subst z
    refine Prod.ext ?_ rfl
    have h' : shrinkingRadius R p depth a y = shrinkingRadius R p depth b y := congrArg Prod.fst he
    have hmono : StrictMonoOn (fun d => shrinkingRadius R p depth d y) (Ioi 0) := by
      intro a ha b hb hab
      exact mul_lt_mul_of_pos_left
        (pow_lt_pow_left₀ (strictMonoOn_softplus_scale (depth y) ha hb hab) (softplus_pos ha _).le hp.ne') hR
    exact hmono.injOn ha hb h'
  have hder (q : ℝ × (X dim)) (hq : q ∈ D) : Function.Bijective (fderiv ℝ f q) := by
    let L := fderiv ℝ h q
    let P := ContinuousLinearMap.snd ℝ ℝ (X dim)
    have hH : HasFDerivAt h L q := ((hh.contDiffAt (ho.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
    have hJ : fderiv ℝ f q = L.prod P := (hH.prodMk P.hasFDerivAt).fderiv
    have hpos : 0 < L (1,0) := by
      have hI : HasDerivAt (fun t : ℝ => (t,q.2)) (1,0) q.1 :=
        (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
      have he := (hH.comp_hasDerivAt q.1 hI).deriv
      change deriv (fun t => shrinkingRadius R p depth t q.2) q.1 = _ at he
      rw [← he]
      exact deriv_shrinkingRadius_parameter_pos hR hq.1 hp depth q.2
    rw [hJ]
    have hI : Function.Injective (L.prod P) := by
      intro a b hab
      have hs := congrArg (fun z : ℝ × (X dim) => z.2) hab
      change a.2 = b.2 at hs
      have hr := congrArg (fun z : ℝ × (X dim) => z.1) hab
      change L a = L b at hr
      have he : a-b = (a.1-b.1) • ((1,0) : ℝ × (X dim)) :=
        Prod.ext (by simp) (by simp [hs])
      have hz : L (a-b) = 0 := by rw [map_sub,hr,sub_self]
      rw [he,map_smul,smul_eq_mul] at hz
      exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hpos.ne')) hs
    exact ⟨hI,(LinearMap.injective_iff_surjective (f := (L.prod P).toLinearMap)).mp hI⟩
  exact exists_smooth_inverse_on_image ho hf hinj hder

end CalderonN
