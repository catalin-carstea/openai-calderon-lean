module

public import Proof.CalderonN.RotatedMultiplierBoundary

import Mathlib.Tactic

/-! Radial trace and multiplication estimates applied to the five
quadratic boundary terms of the rotated multiplication defect. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Gradient
set_option autoImplicit false
set_option maxHeartbeats 6800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_rotated_multiplier_boundary_half_bound (hn : 3 ≤ dim)
    (W D V E m f w₀ dw t₁ e : SmoothData dim)
    (r C J K₀ K₁ K₂ K₃ : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    (hJets : ∀ z ∈ ball (0 : X dim) 1,
      (|W.1 z| ≤ C ∧ ‖fderiv ℝ W.1 z‖ ≤ C) ∧
      (|D.1 z| ≤ C*r ∧ ‖fderiv ℝ D.1 z‖ ≤ C*r) ∧
      (|V.1 z| ≤ C*r ∧ ‖fderiv ℝ V.1 z‖ ≤ C*r) ∧
      (|E.1 z| ≤ C*r^2 ∧ ‖fderiv ℝ E.1 z‖ ≤ C*r^2) ∧
      (|fderiv ℝ m.1 z z| ≤ J ∧ ‖fderiv ℝ (fun x => fderiv ℝ m.1 x x) z‖ ≤ J)) :
    let H := ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) f‖
    let L := 2*Real.sqrt ((dim:ℝ)+3)
    let S := Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))
    ‖smoothBallSobolev 2 w₀‖ ≤ K₀*J*H → ‖smoothBallSobolev 2 dw‖ ≤ K₁*J*r*H →
    ‖smoothBallSobolev 2 t₁‖ ≤ K₂*J*H → ‖smoothBallSobolev 2 e‖ ≤ K₃*J*r^2*H →
    ∃ Z : SmoothData dim,
      Z.1 = (fun z => W.1 z*fderiv ℝ e.1 z z+r*D.1 z*fderiv ℝ t₁.1 z z+
        V.1 z*fderiv ℝ dw.1 z z+E.1 z*fderiv ℝ w₀.1 z z+E.1 z*(fderiv ℝ m.1 z z*f.1 z)) ∧
      ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) Z‖ ≤
        (L*C*S*(K₀+K₁+K₂+K₃)+L^2*C)*J*r^2*H := by
  dsimp only
  intro hw₀ hdw ht₁ he
  let H := ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) f‖
  let L := 2*Real.sqrt ((dim:ℝ)+3)
  let S := Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))
  let B := smoothBoundarySobolevLinear hn (1/2:ℝ) (by norm_num)
  let data (v : SmoothData dim) := (⟨v.1,v.2⟩ : smoothBallDataSubmodule dim)
  let M := smoothBallRadialDerivative m
  let A₁ := data (smoothDataMul W (smoothBallRadialDerivative e))
  let A₂ := data (smoothDataMul D (smoothBallRadialDerivative t₁))
  let A₃ := data (smoothDataMul V (smoothBallRadialDerivative dw))
  let A₄ := data (smoothDataMul E (smoothBallRadialDerivative w₀))
  let A₅ := data (smoothDataMul E (smoothDataMul M f))
  let Q := A₁+r • A₂+A₃+A₄+A₅
  let Z : SmoothData dim := ⟨Q.1,smoothBallData_contDiff Q⟩
  refine ⟨Z,?_,?_⟩
  · funext z
    change W.1 z*fderiv ℝ e.1 z z+r*(D.1 z*fderiv ℝ t₁.1 z z)+
      V.1 z*fderiv ℝ dw.1 z z+E.1 z*fderiv ℝ w₀.1 z z+E.1 z*(fderiv ℝ m.1 z z*f.1 z) = _
    ring
  have hMul (a u : SmoothData dim) (C' : ℝ) (hC' : 0 ≤ C')
      (hJet : ∀ z ∈ ball (0 : X dim) 1, |a.1 z| ≤ C' ∧ ‖fderiv ℝ a.1 z‖ ≤ C') :
      ‖B (data (smoothDataMul a u))‖ ≤ L*C'*‖B (data u)‖ := by
    apply norm_smoothBoundarySobolev_mul_half_le hn a u hC'
    · exact fun z hz => (hJet z hz).1
    · intro z hz
      rw [gradient,LinearIsometryEquiv.norm_map]
      exact (hJet z hz).2
  have hTrace (a u : SmoothData dim) (G G' : ℝ) (hG : 0 ≤ G)
      (ha : ∀ z ∈ ball (0 : X dim) 1, |a.1 z| ≤ G ∧ ‖fderiv ℝ a.1 z‖ ≤ G)
      (hu : ‖smoothBallSobolev 2 u‖ ≤ G') :
      ‖B (data (smoothDataMul a (smoothBallRadialDerivative u)))‖ ≤ L*G*(S*G') :=
    (hMul a _ G hG ha).trans (mul_le_mul_of_nonneg_left
      ((norm_smoothBallRadialDerivative_half_le hn u).trans
        (mul_le_mul_of_nonneg_left hu (by positivity))) (by positivity))
  have h₁ : ‖B A₁‖ ≤ L*C*(S*(K₃*J*r^2*H)) :=
    hTrace W e C _ hC (fun z hz => (hJets z hz).1) he
  have h₂ : ‖B A₂‖ ≤ L*(C*r)*(S*(K₂*J*H)) :=
    hTrace D t₁ (C*r) _ (by positivity) (fun z hz => (hJets z hz).2.1) ht₁
  have h₃ : ‖B A₃‖ ≤ L*(C*r)*(S*(K₁*J*r*H)) :=
    hTrace V dw (C*r) _ (by positivity) (fun z hz => (hJets z hz).2.2.1) hdw
  have h₄ : ‖B A₄‖ ≤ L*(C*r^2)*(S*(K₀*J*H)) :=
    hTrace E w₀ (C*r^2) _ (by positivity) (fun z hz => (hJets z hz).2.2.2.1) hw₀
  have h₅ : ‖B A₅‖ ≤ L*(C*r^2)*(L*J*H) :=
    (hMul E _ (C*r^2) (by positivity) (fun z hz => (hJets z hz).2.2.2.1)).trans
      (mul_le_mul_of_nonneg_left (hMul M f J hJ (fun z hz => (hJets z hz).2.2.2.2)) (by positivity))
  change ‖B Q‖ ≤ _
  simp only [Q,map_add,map_smul]
  calc
    _ ≤ ‖B A₁‖+r*‖B A₂‖+‖B A₃‖+‖B A₄‖+‖B A₅‖ := by
      rw [← norm_smul_of_nonneg hr]
      refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
      exact norm_add_le _ _
    _ ≤ L*C*(S*(K₃*J*r^2*H))+r*(L*(C*r)*(S*(K₂*J*H)))+
        L*(C*r)*(S*(K₁*J*r*H))+L*(C*r^2)*(S*(K₀*J*H))+L*(C*r^2)*(L*J*H) :=
      add_le_add (add_le_add (add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hr)) h₃) h₄) h₅
    _ = _ := by ring

end CalderonN
