import Proof.UniformPhysicalPrincipalData
import Proof.ActualFrameFirstAdjointError
import Proof.UniformPhysicalCoarseAxisFirstErrorBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma PhysicalPrincipalData.coarse_first_error_smooth {Y Ω : Set X} {d : Data} {CF CT : ℝ}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hK : 0 < K) (i : I) :
    ContDiffOn ℝ ∞ (actualFrameFirstAdjointErrorFamily d P.adjoint P.center i) Y := by
  exact contDiffOn_actualFrameFirstAdjointErrorFamily d P.adjoint P.center
    (fun j => (hd.1.2.2.2.2.2.2.1 j).mono hSub)
    (fun a => contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 hK
      hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) P.adjoint (P.center a)
      P.adjoint_smooth (P.center_smooth a)) i

/-- The supplied closed coarse remainder estimate transfers to ANY chosen
actual center-adjoint witnesses by uniqueness. No interpolation or phantom
Sobolev type identity is used to obtain the H1-to-L2 bound. -/
theorem uniform_physical_coarse_first_error_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      (∀ i,ContDiffOn ℝ ∞ (actualFrameFirstAdjointErrorFamily d P.adjoint P.center i) Y) ∧
      ∀ i : I,∀ y ∈ Y,‖actualFrameFirstAdjointErrorFamily d P.adjoint P.center i y‖ ≤ CE*d.radius y := by
  obtain ⟨η,CE,hη,hη1,hCE,hAxis⟩ :=
    uniform_physical_coarse_axis_first_error_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,3*K*CE,hη,hη1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  refine ⟨P.coarse_first_error_smooth hd hY hΩ hSub (zero_lt_one.trans_le hK),?_⟩
  intro i y hy
  exact norm_actualFrameFirstAdjointErrorFamily_le hSub hK d hd.1 P.adjoint P.center CE
    (hAxis floor hf ε hε hSmall d hd CF CT P) i hy

end ShrinkingSpheres
