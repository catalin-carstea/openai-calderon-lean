import Proof.ParallelFirstPotentialComplex
import Proof.ParallelNormAssemblyReservedPotentialParts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
namespace ShrinkingSpheres.ParallelEnergy

/-- Assemble only after all physical/Green/bounded/defect integrals are
known. This proves cubic integrability from the exact identity, without
asserting measurability of pointwise higher commutator choices. -/
lemma firstPotential_integral_assembly (μ : Measure X) (f p b c d : X → ℝ)
    {CP CB CC CD ε E : ℝ} (hCP : 0 ≤ CP) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hCD : 0 ≤ CD)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E)
    (hF : Integrable f μ) (hP : Integrable p μ) (hB : Integrable b μ) (hD : Integrable d μ)
    (hSplit : ∀ᵐ y ∂μ,f y=p y+b y-c y-d y)
    (hPN : |∫ y,p y ∂μ| ≤ CP*ε*E)
    (hBN : |∫ y,b y ∂μ| ≤ CB*ε^2*E)
    (hDN : |∫ y,d y ∂μ| ≤ CD*ε^2*E)
    (hCN : Integrable c μ → |∫ y,c y ∂μ| ≤ CC*ε^2*E) :
    Integrable c μ ∧ |∫ y,f y ∂μ| ≤ (CP+CB+CC+CD)*ε*E := by
  have hC : Integrable c μ := (((hP.add hB).sub hD).sub hF).congr (by
    filter_upwards [hSplit] with y hy
    dsimp only [Pi.sub_apply,Pi.add_apply]
    linarith only [hy])
  have hInt : (∫ y,f y ∂μ)=(∫ y,p y ∂μ)+(∫ y,b y ∂μ)-(∫ y,c y ∂μ)-(∫ y,d y ∂μ) := by
    calc
      _ = ∫ y,((p y+b y)-c y)-d y ∂μ := integral_congr_ae hSplit
      _ = _ := by
        have h1 := integral_sub ((hP.add hB).sub hC) hD
        have h2 := integral_sub (hP.add hB) hC
        have h3 := integral_add hP hB
        simp only [Pi.sub_apply,Pi.add_apply] at h1 h2 h3
        linarith only [h1,h2,h3]
  have hε2 : ε^2 ≤ ε := by nlinarith only [hε,hε1]
  have hWeak (C : ℝ) (hC0 : 0 ≤ C) : C*ε^2*E ≤ C*ε*E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε2 hC0) hE
  refine ⟨hC,?_⟩
  rw [hInt]
  calc
    _ ≤ |(∫ y,p y ∂μ)+(∫ y,b y ∂μ)-(∫ y,c y ∂μ)|+|∫ y,d y ∂μ| := abs_sub _ _
    _ ≤ (|(∫ y,p y ∂μ)+(∫ y,b y ∂μ)|+|∫ y,c y ∂μ|)+|∫ y,d y ∂μ| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((|∫ y,p y ∂μ|+|∫ y,b y ∂μ|)+|∫ y,c y ∂μ|)+|∫ y,d y ∂μ| :=
      add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ ((CP*ε*E+CB*ε^2*E)+CC*ε^2*E)+CD*ε^2*E :=
      add_le_add (add_le_add (add_le_add hPN hBN) (hCN hC)) hDN
    _ ≤ ((CP*ε*E+CB*ε*E)+CC*ε*E)+CD*ε*E :=
      add_le_add (add_le_add (add_le_add le_rfl (hWeak CB hCB)) (hWeak CC hCC)) (hWeak CD hCD)
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
