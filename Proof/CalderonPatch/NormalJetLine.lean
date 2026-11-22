module

public import Proof.CalderonPatch.FiniteNormalJetCalculus
public import Proof.CalderonPatch.BoundaryWaveFace

import Proof.CalderonPatch.CauchyNormalJets
import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

public section
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I axis chartDerivativeWord coordDeriv contDiffOn_coordDeriv)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)

/-- The unnormalized pure normal jet in the signed chart. -/
@[expose] def normalJetAt (f : Z → ℝ) (k : ℕ) (y : Y) : ℝ :=
  iteratedDeriv k (fun t : ℝ => f (signedLayerCoordinates (y,t))) 0

theorem normalFaceTaylor_eq_normalJetAt (f : Z → ℝ) (k : ℕ) (y : Y) :
    normalFaceTaylor f k y = (normalJetAt f k y : ℂ) / (k.factorial : ℂ) :=
  rfl

theorem normalFaceTaylor_congr_normalJetAt {f₁ f₂ : Z → ℝ} {k : ℕ} {y : Y}
    (h : normalJetAt f₁ k y = normalJetAt f₂ k y) :
    normalFaceTaylor f₁ k y = normalFaceTaylor f₂ k y := by
  rw [normalFaceTaylor_eq_normalJetAt,normalFaceTaylor_eq_normalJetAt,h]

private theorem normalLine_hasDerivAt (y : Y) (t : ℝ) :
    HasDerivAt (fun s : ℝ => signedLayerCoordinates (y,s)) (axis (0 : I (n+1))) t := by
  have h := signedLayerCoordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))
  have he : signedLayerCoordinates.toContinuousLinearMap ((0 : Y),(1 : ℝ)) = axis (0 : I (n+1)) :=
    signedLayerCoordinates_axis_normal
  rw [he] at h
  exact h

theorem deriv_normalLine {O : Set Z} (hO : IsOpen O) {f : Z → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) {y : Y} {t : ℝ} (ht : signedLayerCoordinates (y,t) ∈ O) :
    deriv (fun s : ℝ => f (signedLayerCoordinates (y,s))) t =
      coordDeriv 0 f (signedLayerCoordinates (y,t)) := by
  have hd := ((hf.contDiffAt (hO.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt
  exact (hd.comp_hasDerivAt t (normalLine_hasDerivAt y t)).deriv

theorem contDiffAt_normalLine {O : Set Z} (hO : IsOpen O) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Z → F} (hf : ContDiffOn ℝ ∞ f O)
    {y : Y} {t : ℝ} (ht : signedLayerCoordinates (y,t) ∈ O) :
    ContDiffAt ℝ ∞ (fun s : ℝ => f (signedLayerCoordinates (y,s))) t :=
  (hf.contDiffAt (hO.mem_nhds ht)).comp t
    (signedLayerCoordinates.contDiff.contDiffAt.comp t (contDiffAt_const.prodMk contDiffAt_id))

theorem contDiffOn_chartDerivativeWord {O : Set Z} (hO : IsOpen O) (L : List (I (n+1)))
    {f : Z → ℝ} (hf : ContDiffOn ℝ ∞ f O) : ContDiffOn ℝ ∞ (chartDerivativeWord L f) O := by
  induction L with
  | nil => exact hf
  | cons i L ih => exact contDiffOn_coordDeriv ih hO i

private theorem iteratedDeriv_normalLine_eq_word {O : Set Z} (hO : IsOpen O) {f : Z → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) (y : Y) (k : ℕ) :
    ∀ t : ℝ, signedLayerCoordinates (y,t) ∈ O →
      iteratedDeriv k (fun s : ℝ => f (signedLayerCoordinates (y,s))) t =
        chartDerivativeWord (List.replicate k 0) f (signedLayerCoordinates (y,t)) := by
  induction k with
  | zero => intro t ht; rfl
  | succ k ih =>
    intro t ht
    have hNear := (normalLine_hasDerivAt y t).continuousAt.eventually_mem (hO.mem_nhds ht)
    have he : iteratedDeriv k (fun s : ℝ => f (signedLayerCoordinates (y,s))) =ᶠ[𝓝 t]
        fun s : ℝ => chartDerivativeWord (List.replicate k 0) f (signedLayerCoordinates (y,s)) :=
      hNear.mono (fun s hs => ih s hs)
    rw [iteratedDeriv_succ, he.deriv_eq,
      deriv_normalLine hO (contDiffOn_chartDerivativeWord hO _ hf) ht]
    rfl

theorem normalJetAt_eq_chartDerivativeWord {O : Set Z} (hO : IsOpen O) {f : Z → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) {y : Y} (hy : normalFacePoint y ∈ O) (k : ℕ) :
    normalJetAt f k y = chartDerivativeWord (List.replicate k 0) f (normalFacePoint y) := by
  have h := iteratedDeriv_normalLine_eq_word hO hf y k 0 (by
    simpa only [signedLayerCoordinates_face] using hy)
  simpa only [normalJetAt,signedLayerCoordinates_face] using h

private theorem chartDerivativeWord_tangent_comm {O : Set Z} (hO : IsOpen O) {f : Z → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) {x : Z} (hx : x ∈ O)
    (L : List (I (n+1))) (i : I (n+1)) :
    chartDerivativeWord L (coordDeriv i f) x = coordDeriv i (chartDerivativeWord L f) x := by
  obtain ⟨g,hg,_,A,hA,hxA,_,he⟩ :=
    CalderonN.exists_contDiff_extension_near_compact hO isCompact_singleton
      (singleton_subset_iff.mpr hx) hf
  have hFG : g =ᶠ[𝓝 x] f := he.eventuallyEq_of_mem (hA.mem_nhds (hxA (mem_singleton x)))
  have hLeft : chartDerivativeWord (L ++ [i]) g x = chartDerivativeWord (L ++ [i]) f x :=
    (chartDerivativeWord_congr_germ _ hFG).eq_of_nhds
  have hRight : chartDerivativeWord (i :: L) g x = chartDerivativeWord (i :: L) f x :=
    (chartDerivativeWord_congr_germ _ hFG).eq_of_nhds
  have hperm : (L ++ [i]).Perm (i :: L) := List.perm_append_comm
  have h := congrFun (CalderonN.chartDerivativeWord_perm hperm hg) x
  have hEq := hLeft.symm.trans (h.trans hRight)
  rw [chartDerivativeWord_append] at hEq
  exact hEq

/-- Equality along the face of one pure normal jet also determines
that jet of each tangential derivative. -/
theorem eqOn_normalJetAt_coordDeriv_tangent {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {f₁ f₂ : Z → ℝ} (hf₁ : ContDiffOn ℝ ∞ f₁ O₁) (hf₂ : ContDiffOn ℝ ∞ f₂ O₂)
    {U : Set Y} (hU : IsOpen U) (h₁ : MapsTo normalFacePoint U O₁)
    (h₂ : MapsTo normalFacePoint U O₂) (k : ℕ) (i : I n)
    (hEq : EqOn (normalJetAt f₁ k) (normalJetAt f₂ k) U) :
    EqOn (normalJetAt (coordDeriv i.succ f₁) k) (normalJetAt (coordDeriv i.succ f₂) k) U := by
  let L := List.replicate k (0 : I (n+1))
  have hFace : normalFacePoint = fun y : Y => signedLayerCoordinates (y,(0 : ℝ)) :=
    funext (fun y => (signedLayerCoordinates_face y).symm)
  have hRead (f : Z → ℝ) {O : Set Z} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
      (hT : MapsTo normalFacePoint U O) (y : Y) (hy : y ∈ U) :
      normalJetAt (coordDeriv i.succ f) k y =
        fderiv ℝ (normalJetAt f k) y (axis i) := by
    have he : normalJetAt f k =ᶠ[𝓝 y] (chartDerivativeWord L f ∘ normalFacePoint) :=
      Filter.mem_of_superset (hU.mem_nhds hy)
        (fun z hz => normalJetAt_eq_chartDerivativeWord hO hf (hT hz) k)
    have hD := ((contDiffOn_chartDerivativeWord hO L hf).contDiffAt
      (hO.mem_nhds (hT hy))).differentiableAt (by simp)
    have hL : HasFDerivAt normalFacePoint
        (signedLayerCoordinates.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Y ℝ)) y := by
      rw [hFace]
      exact signedLayerCoordinates.toContinuousLinearMap.hasFDerivAt.comp y
        ((hasFDerivAt_id y).prodMk (hasFDerivAt_const (0 : ℝ) y))
    rw [normalJetAt_eq_chartDerivativeWord hO (contDiffOn_coordDeriv hf hO i.succ) (hT hy),
      chartDerivativeWord_tangent_comm hO hf (hT hy), he.fderiv_eq,
      (hD.hasFDerivAt.comp y hL).fderiv]
    change coordDeriv i.succ (chartDerivativeWord L f) (normalFacePoint y) =
      fderiv ℝ (chartDerivativeWord L f) (normalFacePoint y) (signedLayerCoordinates (axis i,0))
    rw [signedLayerCoordinates_axis_tangent]
    rfl
  intro y hy
  have h : fderiv ℝ (normalJetAt f₁ k) y = fderiv ℝ (normalJetAt f₂ k) y :=
    (hEq.eventuallyEq_of_mem (hU.mem_nhds hy)).fderiv_eq
  rw [hRead _ hO₁ hf₁ h₁ y hy,hRead _ hO₂ hf₂ h₂ y hy,h]

end CalderonPatch.BoundaryLayer
