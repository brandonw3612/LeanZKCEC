import LeanZKCEC.Logic.Vars

namespace LeanZKCEC

namespace CNF

theorem disjoint_projections {Φ Ψ : CNF}
  (h : (Φ ∪ Ψ).Unsatisfiable) :
  ∀ {ω}, ¬ (Φ.ProjSat ω (Φ.vars ∩ Ψ.vars) ∧
            Ψ.ProjSat ω (Φ.vars ∩ Ψ.vars)) := by
  unfold ProjSat
  intro ω h_ps
  obtain ⟨⟨σ, hσ, h_eqσ⟩, ⟨τ, hτ, h_eqτ⟩⟩ := h_ps
  have h_eq : Set.EqOn σ τ (Φ.vars ∩ Ψ.vars) := by
    intro v hv
    rw [← Finset.coe_inter, Finset.mem_coe] at hv
    exact (h_eqσ hv).trans (h_eqτ hv).symm
  rw [CNF.unsat_iff] at h
  exact h (CNF.sat_union_glue hσ hτ h_eq)

theorem unsat_of_disjoint_projections {Φ Ψ : CNF}
  (h : ∀ {ω}, ¬ (Φ.ProjSat ω (Φ.vars ∩ Ψ.vars) ∧
                 Ψ.ProjSat ω (Φ.vars ∩ Ψ.vars))) :
  (Φ ∪ Ψ).Unsatisfiable := by
  rw [CNF.unsat_iff]
  intro ω hω
  rw [CNF.sat_union] at hω
  obtain ⟨hΦ, hΨ⟩ := hω
  apply h
  exact ⟨CNF.projSat_of_sat hΦ, CNF.projSat_of_sat hΨ⟩

theorem unsat_iff_disjoint_projection {Φ Ψ : CNF} :
  (Φ ∪ Ψ).Unsatisfiable ↔
  ∀ {ω}, ¬ (Φ.ProjSat ω (Φ.vars ∩ Ψ.vars) ∧
             Ψ.ProjSat ω (Φ.vars ∩ Ψ.vars)) := by
  exact ⟨disjoint_projections, unsat_of_disjoint_projections⟩

end CNF

theorem lemma_41 {Φ Ψ : CNF}
  (hΦ : Φ.Satisfiable) (hΨ : Ψ.Satisfiable) (hΦΨ : (Φ ∪ Ψ).Unsatisfiable) :
  {ω | Φ.ProjSat ω (Φ.vars ∩ Ψ.vars)} ∩
  {ω | Ψ.ProjSat ω (Φ.vars ∩ Ψ.vars)} = ∅ := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
             Set.mem_empty_iff_false, iff_false]
  exact CNF.disjoint_projections hΦΨ

end LeanZKCEC
