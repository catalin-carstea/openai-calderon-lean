module

public import Proof.CalderonN.NormalPhase
public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.FramePullback
public import Proof.CalderonN.ShrinkingRadiusParameter
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

public import Proof.CalderonN.SphereCoordinates
import Proof.CalderonN.FrameOperators
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev NormalSphereBase (dim : ℕ) := (X dim) × ↥(standardSphere dim)

/-- The actual normal sphere at a positive regularization parameter. -/
@[expose] def normalSpherePoint (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (r : ℝ → (X dim) → ℝ) (q : (NormalSphereBase dim) × ℝ) : (X dim) × (X dim) :=
  (E (q.1.1, r q.2 q.1.1 • frameVector e q.1.1 (q.1.2 : (X dim))),q.1.1)

set_option maxHeartbeats 2000000 in
/-- The positive regularization parameter is a genuine vertical coordinate
on the punctured part of the actual normal tube. -/
theorem exists_normalSphereCoordinates
    {Y : Set (X dim)} (hY : IsOpen Y) {γ : (MetricField dim)} (hγ : SmoothMetric Y γ)
    {ρ : ℝ} (hρ : 0 < ρ) {E V : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : IsOpen (normalPairDomain Y γ ρ E))
    (hV : ContDiffOn ℝ ∞ V (normalPairDomain Y γ ρ E))
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {e : (Frame dim)} (he : ∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {depth : (X dim) → ℝ} (hd : ContDiffOn ℝ ∞ depth Y)
    {R : ℝ} (hR : 0 < R) {p : ℕ} (hp : 0 < p) :
    let r := shrinkingRadius R p depth
    ∃ c : OpenPartialHomeomorph ((X dim) × (X dim)) ((NormalSphereBase dim) × ℝ),
      c.source ⊆ normalPairDomain Y γ ρ E ∧
      c.target = {z | z.1.1 ∈ Y ∧ 0 < z.2 ∧ r z.2 z.1.1 < ρ} ∧
      ∀ z : (NormalSphereBase dim) × ℝ, c.symm z = normalSpherePoint E e r z := by
  let r := shrinkingRadius R p depth
  let D := normalPairDomain Y γ ρ E
  let H := Ioi (0 : ℝ) ×ˢ Y
  let f := shrinkingRadiusParameterMap R p depth
  let J := f '' H
  obtain ⟨hJ,recover,hRecover,hLeft,hMap,hRight⟩ := exists_inverse_shrinkingRadius_parameter hY hd hR hp
  let coeff (q : (X dim) × (X dim)) := frameCoordinates γ q.2 (e q.2) (V q)
  let rad (q : (X dim) × (X dim)) := (‖coeff q‖,q.2)
  let S := D ∩ rad ⁻¹' J
  let T₀ : Set ((NormalSphereBase dim) × ℝ) := (Y ×ˢ univ) ×ˢ Ioi (0 : ℝ)
  let rval (z : (NormalSphereBase dim) × ℝ) := r z.2 z.1.1
  let T := T₀ ∩ rval ⁻¹' Iio ρ
  let toFun (q : (X dim) × (X dim)) : (NormalSphereBase dim) × ℝ :=
    ((q.2,sphereDirection (coeff q)), (recover (rad q)).1)
  let invFun := normalSpherePoint E e r
  have hCenter : MapsTo Prod.snd D Y := fun q hq => (hInv q hq).1.1
  have hcoeff : ContDiffOn ℝ ∞ coeff D := by
    apply (contDiffOn_piLp 2).mpr
    intro k
    change ContDiffOn ℝ ∞ (fun q : (X dim) × (X dim) => metricPair γ q.2 (V q) (e q.2 k)) D
    unfold metricPair
    refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
    have hi : ContDiffOn ℝ ∞ (fun q : (X dim) × (X dim) => V q i) D :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hV
    have hj : ContDiffOn ℝ ∞ (fun q : (X dim) × (X dim) => e q.2 k j) D :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn (he k)).comp
        contDiff_snd.contDiffOn hCenter
    exact ((((hγ.1 i j).comp contDiff_snd.contDiffOn hCenter).mul hi).mul hj)
  have hRad : ContinuousOn rad D := hcoeff.continuousOn.norm.prodMk continuous_snd.continuousOn
  have hS : IsOpen S := hRad.isOpen_inter_preimage hN hJ
  have hT₀ : IsOpen T₀ := (hY.prod isOpen_univ).prod isOpen_Ioi
  have hRbase : Continuous (fun z : (NormalSphereBase dim) × ℝ => (z.2,z.1.1)) :=
    continuous_snd.prodMk continuous_fst.fst
  have hrv : ContinuousOn rval T₀ :=
    (contDiffOn_shrinkingRadius_parameter hd R p).continuousOn.comp
      hRbase.continuousOn (fun z hz => ⟨hz.2,hz.1.1⟩)
  have hT : IsOpen T := hrv.isOpen_inter_preimage hT₀ isOpen_Iio
  have hpos (s : ℝ) (hs : 0 < s) (y : (X dim)) : 0 < r s y :=
    mul_pos hR (pow_pos (softplus_pos hs _) _)
  have hRec (q : (X dim) × (X dim)) (hq : q ∈ S) :
      0 < (recover (rad q)).1 ∧ r (recover (rad q)).1 q.2 = ‖coeff q‖ := by
    have hrq := hRight hq.2
    have hys : (recover (rad q)).2 = q.2 := congrArg Prod.snd hrq
    have hr : r (recover (rad q)).1 (recover (rad q)).2 = ‖coeff q‖ :=
      congrArg Prod.fst hrq
    exact ⟨(hMap hq.2).1,hys ▸ hr⟩
  have hNonzero (q : (X dim) × (X dim)) (hq : q ∈ S) : coeff q ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [← (hRec q hq).2]
    exact (hpos _ (hRec q hq).1 _).ne'
  have hTo : MapsTo toFun S T := by
    intro q hq
    have hy := hCenter hq.1
    refine ⟨⟨⟨hy,mem_univ _⟩,(hRec q hq).1⟩,?_⟩
    change r (recover (rad q)).1 q.2 < ρ
    rw [(hRec q hq).2]
    have h := (hInv q hq.1).1.2
    change metricPair γ q.2 (V q) (V q) < ρ^2 at h
    rw [← norm_frameCoordinates_sq γ q.2 (V q) (e q.2) (hframe q.2 hy)] at h
    exact (sq_lt_sq₀ (norm_nonneg _) hρ.le).mp h
  have hInvData (z : (NormalSphereBase dim) × ℝ) (hz : z ∈ T) :
      invFun z ∈ D ∧ coeff (invFun z) = rval z • (z.1.2 : (X dim)) ∧
        rad (invFun z) = f (z.2,z.1.1) := by
    let y := z.1.1
    let w := (z.1.2 : (X dim))
    let v := rval z • frameVector e y w
    have hZ : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp z.1.2.property
    have hy : y ∈ Y := hz.1.1.1
    have hr : 0 < rval z := hpos _ hz.1.2 _
    have hc : frameCoordinates γ y (e y) v = rval z • w := by
      rw [← frameCoordinatesL_apply,show v = rval z • frameVectorL (e y) w by
        rw [frameVectorL_apply (e y) w y]; rfl,
        map_smul,frameCoordinatesL_frameVectorL γ y (e y) (hframe y hy)]
    have hVdom : (y,v) ∈ normalVelocityDomain Y γ ρ := by
      refine ⟨hy,?_⟩
      change metricPair γ y v v < ρ^2
      rw [← norm_frameCoordinates_sq γ y v (e y) (hframe y hy),hc,norm_smul,
        Real.norm_eq_abs,abs_of_pos hr,hZ,mul_one]
      exact (sq_lt_sq₀ hr.le hρ.le).mpr hz.2
    have hXin : invFun z ∈ D := ⟨(y,v),hVdom,rfl⟩
    have hCoef : coeff (invFun z) = rval z • w := by
      change frameCoordinates γ y (e y) (V (E (y,v),y)) = _
      rw [hExact (y,v) hVdom,hc]
    refine ⟨hXin,hCoef,Prod.ext ?_ rfl⟩
    change ‖coeff (invFun z)‖ = rval z
    rw [hCoef,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hZ,mul_one]
  have hInvTo : MapsTo invFun T S := fun z hz =>
    ⟨(hInvData z hz).1,⟨(z.2,z.1.1),⟨hz.1.2,hz.1.1.1⟩,(hInvData z hz).2.2.symm⟩⟩
  have hL : LeftInvOn invFun toFun S := by
    intro q hq
    have hy := hCenter hq.1
    have hV' := hInv q hq.1
    have hc := (hRec q hq).2
    apply Prod.ext
    · change E (q.2, r (recover (rad q)).1 q.2 •
        frameVector e q.2 (sphereDirection (coeff q) : (X dim))) = q.1
      rw [hc,sphereDirection_val (hNonzero q hq)]
      have hf : frameVector e q.2 (‖coeff q‖⁻¹ • coeff q) =
          ‖coeff q‖⁻¹ • frameVector e q.2 (coeff q) := by
        rw [← frameVectorLinear_apply, map_smul, frameVectorLinear_apply]
      rw [hf,smul_inv_smul₀ (norm_ne_zero_iff.mpr (hNonzero q hq))]
      change E (q.2,frameVector (fun _ => e q.2) q.2
        (frameCoordinates γ q.2 (e q.2) (V q))) = q.1
      rw [frameVector_frameCoordinates _ _ _ _ (hframe q.2 hy)]
      exact hV'.2
    · rfl
  have hRinv : RightInvOn invFun toFun T := by
    intro z hz
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        change (sphereDirection (coeff (invFun z)) : (X dim)) = (z.1.2 : (X dim))
        rw [(hInvData z hz).2.1]
        exact sphereDirection_pos_smul (mem_sphere_zero_iff_norm.mp z.1.2.property) (hpos _ hz.1.2 _)
    · change (recover (rad (invFun z))).1 = z.2
      rw [(hInvData z hz).2.2,hLeft (show (z.2,z.1.1) ∈ H from ⟨hz.1.2,hz.1.1.1⟩)]
  have hCont : ContinuousOn toFun S := by
    have hc : ContinuousOn coeff S := hcoeff.continuousOn.mono inter_subset_left
    have hp : ContinuousOn rad S := hRad.mono inter_subset_left
    have hDir := continuousOn_sphereDirection.comp hc (fun q hq h =>
      hNonzero q hq (mem_singleton_iff.mp h))
    have hParam := (hRecover.continuousOn.comp hp (fun q hq => hq.2)).fst
    exact (continuous_snd.continuousOn.prodMk hDir).prodMk hParam
  have hContInv : ContinuousOn invFun T := by
    have hvel : ContinuousOn (fun z : (NormalSphereBase dim) × ℝ =>
        frameVector e z.1.1 (z.1.2 : (X dim))) T := by
      unfold frameVector
      refine continuousOn_finsetSum _ fun i _ => ?_
      have hSphere := (continuous_subtype_val.comp (continuous_snd.comp continuous_fst) :
        Continuous (fun z : (NormalSphereBase dim) × ℝ => (z.1.2 : (X dim))))
      exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hSphere).continuousOn.smul
        ((he i).continuousOn.comp continuous_fst.fst.continuousOn (fun z hz => hz.1.1.1))
    exact (hE.continuous.comp_continuousOn (continuous_fst.fst.continuousOn.prodMk
      ((hrv.mono inter_subset_left).smul hvel))).prodMk continuous_fst.fst.continuousOn
  let c : OpenPartialHomeomorph ((X dim) × (X dim)) ((NormalSphereBase dim) × ℝ) :=
    { toFun := toFun
      invFun := invFun
      source := S
      target := T
      map_source' := hTo
      map_target' := hInvTo
      left_inv' := hL
      right_inv' := hRinv
      open_source := hS
      open_target := hT
      continuousOn_toFun := hCont
      continuousOn_invFun := hContInv }
  refine ⟨c,inter_subset_left,?_ ,fun _ => rfl⟩
  ext z
  change ((z.1.1 ∈ Y ∧ z.1.2 ∈ (univ : Set ↥(standardSphere dim))) ∧ 0 < z.2) ∧ rval z < ρ ↔ _
  simp only [mem_univ,mem_ofPred_eq,and_true,and_assoc,rval,r]

end CalderonN
