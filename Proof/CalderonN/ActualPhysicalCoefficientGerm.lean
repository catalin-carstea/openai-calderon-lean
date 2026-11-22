module

public import Proof.CalderonN.ActualSupportedConormal
public import Proof.CalderonN.ActualRelativeCoefficientGerms

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.LocalMixedParameterJetCalculus
import Mathlib.Tactic

/-! Physical-radius local coefficient extensions for the classical
parametric Poisson problem on the common supported trace core. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_physicalCoefficient_germ (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∃ (V : Set (X dim)) (a : X dim × X dim → Mat dim) (J : Set (X dim)),
        IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧ ContDiff ℝ ∞ a ∧ IsCompact J ∧
        (∀ x z,z ∉ J → a (x,z) = 0) ∧
        ∀ x ∈ V, EqOn (fun z => a (x,z))
          (fun z => firstNormalVelocityCoefficient d x (d.radius x • frameVector d.frame x z))
          (closedBall (0:X dim) 1) := by
  obtain ⟨η,_,_,hη,_,_,hG⟩ := uniform_actual_relativeCoefficient_germs hn hY hΩ hYc 0
    hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε he hs d hd hF y hy
  obtain ⟨a₁,a₂,J₁,W,ha₁,ha₂,hJ₁,hSupp,hW,hKW,_,_,hEq,_⟩ := hG floor hf ε he hs d hd hF y hy
  let C := closedBall (0:X dim) 1
  have hC : IsCompact C := isCompact_closedBall _ _
  let r := d.radius y
  have hr : r ≠ 0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  obtain ⟨R,hR,hRR⟩ := exists_global_smooth_germ_of_open d.radius hY hd.2.2.2.2.1.1 hy
  have hNear : {x | R x = d.radius x} ∩ Y ∈ 𝓝 y := hRR.and (hY.mem_nhds hy)
  obtain ⟨G,hGsub,hGopen,hyG⟩ := _root_.mem_nhds_iff.mp hNear
  have hRRy : R y = r := (hGsub hyG).1
  let p (q : X dim × X dim) : FramedRadialParameter dim := ((q.1,R q.1/r-1),q.2)
  have hp : ContDiff ℝ ∞ p :=
    (contDiff_fst.prodMk (((hR.comp contDiff_fst).div contDiff_const (fun _ => hr)).sub
      contDiff_const)).prodMk contDiff_snd
  have hW' : IsOpen (p ⁻¹' W) := hW.preimage hp.continuous
  have hCW : {y} ×ˢ C ⊆ p ⁻¹' W := by
    intro q hq
    have hqy : q.1 = y := hq.1
    apply hKW
    refine ⟨?_,hq.2⟩
    change (q.1,R q.1/r-1) = (y,0)
    rw [hqy,hRRy,div_self hr,sub_self]
  obtain ⟨U,L,hU,_,hyU,hCL,hUL⟩ := generalized_tube_lemma
    (isCompact_singleton (x:=y)) hC hW' hCW
  let V := U ∩ G
  have hV : IsOpen V := hU.inter hGopen
  have hyV : y ∈ V := ⟨hyU (mem_singleton _),hyG⟩
  obtain ⟨A₀,hA₀,hA₀K,B,_,hCB,_,hA₀E⟩ := exists_contDiff_extension_near_compact
    (isOpen_univ : IsOpen (univ : Set (X dim))) hC (subset_univ C)
    (show ContDiffOn ℝ ∞ (fun _ : X dim => (1 : Mat dim)) univ from contDiffOn_const)
  let J := J₁ ∪ tsupport A₀
  let a (q : X dim × X dim) := A₀ q.2+r • a₁ (p q)+r^2 • a₂ (p q)
  have ha : ContDiff ℝ ∞ a :=
    ((hA₀.comp contDiff_snd).add ((ha₁.comp hp).const_smul _)).add ((ha₂.comp hp).const_smul _)
  refine ⟨V,a,J,hV,hyV,fun _ h => (hGsub h.2).2,ha,hJ₁.union hA₀K.isCompact,?_,?_⟩
  · intro x z hz
    have hz₁ : z ∉ J₁ := fun h => hz (Or.inl h)
    have hz₀ : z ∉ tsupport A₀ := fun h => hz (Or.inr h)
    change A₀ z+r • a₁ ((p (x,z)).1,z)+r^2 • a₂ ((p (x,z)).1,z) = 0
    rw [image_eq_zero_of_notMem_tsupport hz₀,(hSupp (p (x,z)).1 z hz₁).1,
      (hSupp (p (x,z)).1 z hz₁).2,smul_zero,smul_zero,add_zero,add_zero]
  intro x hx z hz
  have hqW : p (x,z) ∈ W := hUL ⟨hx.1,hCL hz⟩
  have hRx : R x = d.radius x := (hGsub hx.2).1
  have hRadius : r*(1+(p (x,z)).1.2) = d.radius x := by
    dsimp only [p]
    rw [show 1+(R x/r-1) = R x/r by ring,div_eq_mul_inv,
      mul_left_comm,mul_inv_cancel₀ hr,mul_one,hRx]
  have hFlat : A₀ z = 1 := hA₀E (hCB hz)
  have hL : a (x,z) = 1+r • a₁ (p (x,z))+r^2 • a₂ (p (x,z)) := by simp only [a,hFlat]
  have hR : firstNormalVelocityCoefficient d x
      ((r*(1+(p (x,z)).1.2)) • frameVector d.frame x z) = _ := hEq (p (x,z)) hqW
  exact hL.trans (hR.symm.trans (congrArg
    (fun s : ℝ => firstNormalVelocityCoefficient d x (s • frameVector d.frame x z)) hRadius))

end CalderonN
