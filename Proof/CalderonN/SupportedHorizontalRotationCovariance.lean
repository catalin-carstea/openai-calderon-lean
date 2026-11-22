module

public import Proof.CalderonN.SmoothSupportedTraceScalarCalculus
public import Proof.CalderonN.SmoothTraceRotationCovariance

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! The horizontal derivative rotates the frame index of the lowering
and raising operators. This gives the exact connection correction
needed when taking the model adjoint. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem sum_skew_rotation_contraction {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Γ : I dim → I dim → ℝ) (hΓ : ∀ i j, Γ i j = -Γ j i) (v : I dim → V) (k : I dim) :
    (∑ i,∑ j, (-(1/2:ℝ)*Γ i j) • ((if k=j then v i else 0)-(if k=i then v j else 0))) =
      ∑ j,Γ k j • v j := by
  classical
  let α (i j : I dim) := -(1/2:ℝ)*Γ i j
  have h₁ (i : I dim) : (∑ j, α i j • (if k=j then v i else 0)) = α i k • v i := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hk
      rw [if_neg (Ne.symm hk),smul_zero]
    · simp
  have h₂ (j : I dim) : (∑ i, α i j • (if k=i then v j else 0)) = α k j • v j := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hk
      rw [if_neg (Ne.symm hk),smul_zero]
    · simp
  change (∑ i,∑ j, α i j • ((if k=j then v i else 0)-(if k=i then v j else 0))) = _
  simp only [smul_sub,Finset.sum_sub_distrib,h₁]
  rw [Finset.sum_comm (f:=fun i j => α i j • (if k=i then v j else 0))]
  simp only [h₂,← Finset.sum_sub_distrib,← sub_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show α j k-α k j = Γ k j by dsimp only [α]; rw [hΓ j k]; ring]

open BallDirichlet TauCeti PDE
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim} {K : ℝ}
  (hY : IsOpen Y) (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
  (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)

include hframe in
theorem supportedHorizontal_comm_rotating_family
    (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y)
    (L : I dim → Module.End ℝ (SmoothSphereTrace dim))
    (hL : ∀ k, SmoothSupportedTraceFiberRegular Y (fun _ => L k))
    (hBase : ∀ k (b : X dim),
      smoothSupportedTraceBaseDiff b * smoothSupportedTraceFiberAction hY (fun _ => L k) (hL k) =
        smoothSupportedTraceFiberAction hY (fun _ => L k) (hL k) * smoothSupportedTraceBaseDiff b)
    (hCov : ∀ i j k : I dim,
      smoothSphereTraceRotation i j * L k-L k * smoothSphereTraceRotation i j =
        (if k=j then L i else 0)-(if k=i then L j else 0)) (k : I dim) :
    let H := supportedHorizontal hY hg hK he a ha
    let S (i : I dim) := smoothSupportedTraceFiberAction hY (fun _ => L i) (hL i)
    H*S k-S k*H = ∑ j : I dim,smoothSupportedTraceBaseMul hY
      (fun x => frameConnectionCoefficient g e x (a x) k j)
      (hg.contDiffOn_frameConnection hY hK e he a ha k j) * S j := by
  classical
  dsimp only
  let S (i : I dim) := smoothSupportedTraceFiberAction hY (fun _ => L i) (hL i)
  let M (i : I dim) := smoothSupportedTraceBaseMul hY (fun x => a x i) (contDiffOn_vector_component a ha i)
  let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let F := ∑ i,M i*D i
  let α (i j : I dim) (x : X dim) := -(1/2:ℝ)*frameConnectionCoefficient g e x (a x) i j
  have hα (i j : I dim) : ContDiffOn ℝ ∞ (α i j) Y :=
    contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK e he a ha i j)
  let U (i j : I dim) := smoothSupportedTraceBaseMul hY (α i j) (hα i j)
  let G := ∑ i : I dim,∑ j : I dim, U i j * supportedRotation hY i j
  have hF : F*S k = S k*F := by
    simp only [F,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hM : M i*S k = S k*M i := smoothSupportedTraceBaseMul_comm_fiber hY _ _ _ _
    have hD : D i*S k = S k*D i := hBase k (axis i)
    calc
      (M i*D i)*S k = M i*(D i*S k) := mul_assoc _ _ _
      _ = (S k*M i)*D i := by rw [hD,← mul_assoc,hM]
      _ = _ := mul_assoc _ _ _
  change (F+G)*S k-S k*(F+G) = _
  rw [add_mul,mul_add,hF,add_sub_add_left_eq_sub]
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  have hG (w : SmoothSupportedTraceSection Y) :
      smoothSupportedTraceFiberL x (G w) =
        ∑ i : I dim,∑ j : I dim, α i j x • smoothSphereTraceRotation i j (smoothSupportedTraceFiberL x w) := by
    simp only [G,U,LinearMap.sum_apply,map_sum,Module.End.mul_apply,
      smoothSupportedTraceBaseMul_fiber,smoothSupportedTraceFiberAction_fiber,supportedRotation]
  have hS (i : I dim) (w : SmoothSupportedTraceSection Y) :
      smoothSupportedTraceFiberL x (S i w) = L i (smoothSupportedTraceFiberL x w) :=
    smoothSupportedTraceFiberAction_fiber hY _ _ w x
  simp only [LinearMap.sub_apply,map_sub,Module.End.mul_apply,hG,hS,LinearMap.sum_apply,map_sum,
    smoothSupportedTraceBaseMul_fiber,map_smul,← Finset.sum_sub_distrib,← smul_sub]
  let v := smoothSupportedTraceFiberL x u
  let Γ (i j : I dim) := frameConnectionCoefficient g e x (a x) i j
  have hRotation (i j : I dim) :
      smoothSphereTraceRotation i j (L k v)-L k (smoothSphereTraceRotation i j v) =
        (if k=j then L i v else 0)-(if k=i then L j v else 0) := by
    have h := congrArg (fun W : Module.End ℝ (SmoothSphereTrace dim) => W v) (hCov i j k)
    split_ifs at h ⊢ <;> simpa only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.zero_apply] using h
  change (∑ i : I dim,∑ j : I dim, α i j x •
    (smoothSphereTraceRotation i j (L k v)-L k (smoothSphereTraceRotation i j v))) =
    ∑ j : I dim,Γ k j • L j v
  simp only [hRotation,α]
  exact sum_skew_rotation_contraction Γ (frameConnection_skew hY hg hK e he hframe hx (a x)) _ k

end CalderonN
