import LeanZKCEC.Logic.Circuit

namespace LeanZKCEC

namespace Tseitin

def gateClauses (v : Variable) : Gate → CNF
  -- (v → ¬a) ∧ (¬a → v)
  | .not a => {
    {⟨v, true⟩, ⟨a, true⟩},               --  v ∨  a
    {⟨v, false⟩, ⟨a, false⟩}              -- ¬v ∨ ¬a
  }
  -- (v → a ∧ b) ∧ (a ∧ b → v)
  | .and a b => {
    {⟨v, false⟩, ⟨a, true⟩},              -- ¬v ∨  a
    {⟨v, false⟩, ⟨b, true⟩},              -- ¬v ∨  b
    {⟨v, true⟩, ⟨a, false⟩, ⟨b, false⟩}   --  v ∨ ¬a ∨ ¬b
  }
  -- (v → a ∨ b) ∧ (a ∨ b → v)
  | .or a b => {
    {⟨v, true⟩, ⟨a, false⟩},              --  v ∨ ¬a
    {⟨v, true⟩, ⟨b, false⟩},              --  v ∨ ¬b
    {⟨v, false⟩, ⟨a, true⟩, ⟨b, true⟩}    -- ¬v ∨  a ∨  b
  }
  -- (v → a ⊕ b) ∧ (a ⊕ b → v)
  | .xor a b => {
    {⟨v, true⟩, ⟨a, false⟩, ⟨b, true⟩},   --  v ∨ ¬a ∨  b
    {⟨v, true⟩, ⟨a, true⟩, ⟨b, false⟩},   --  v ∨  a ∨ ¬b
    {⟨v, false⟩, ⟨a, true⟩, ⟨b, true⟩},   -- ¬v ∨  a ∨  b
    {⟨v, false⟩, ⟨a, false⟩, ⟨b, false⟩}  -- ¬v ∨ ¬a ∨ ¬b
  }

theorem sat_gateClauses {ω : Assignment} {v : Variable} {g : Gate} :
  (gateClauses v g).Sat ω ↔ ω v = g.eval ω := by
  cases g with (
    next a =>
    simp [gateClauses, CNF.Sat, Clause.Sat, Literal.eval, Gate.eval]
    cases hv : ω v <;> cases ha : ω a <;> simp
  )

theorem vars_gateClauses {v v' : Variable} {g : Gate}
  (h : v' ∈ (gateClauses v g).vars) :
  v' = v ∨ v' ∈ g.args := by
  cases g with (
    simp [gateClauses] at h
    simp [Gate.args]
    tauto
  )

end Tseitin

def tseitinGates : GateList → CNF
  | [] => ∅
  | (v, g) :: rest => Tseitin.gateClauses v g ∪ tseitinGates rest

def tseitin (C : Circuit) : CNF := tseitinGates C.gates

theorem sat_tseitinGates {ω : Assignment} :
  ∀ {gl : GateList}, (tseitinGates gl).Sat ω ↔ GatesConsistent ω gl
  | [] => by simp [tseitinGates, GatesConsistent]
  | (v, g) :: rest => by
    unfold tseitinGates
    rw [CNF.sat_union, Tseitin.sat_gateClauses, sat_tseitinGates]
    exact GatesConsistent.cons.symm

theorem sat_tseitin {ω : Assignment} {C : Circuit} :
  (tseitin C).Sat ω ↔ C.Consistent ω := by
  unfold tseitin Circuit.Consistent
  induction C.gates with
  | nil =>
    simp [tseitinGates, GatesConsistent]
  | cons p rest ih =>
    obtain ⟨v, g⟩ := p
    unfold tseitinGates
    rw [CNF.sat_union, ih, Tseitin.sat_gateClauses]
    unfold GatesConsistent
    simp [List.mem_cons, or_imp, forall_and]

theorem tseitin_satisfiable {C : Circuit}
  (hC : C.WellFormed) :
  (tseitin C).Satisfiable := by
  unfold CNF.Satisfiable
  let F := Function.const Variable false
  use C.run F
  rw [sat_tseitin]
  exact hC.run_consistent

theorem tseitin_total {C : Circuit} {ω : Assignment}
  (hC : C.WellFormed) :
  (tseitin C).ProjSat ω C.inputs.toFinset := by
  unfold CNF.ProjSat
  use C.run ω
  constructor
  · rw [sat_tseitin]
    exact hC.run_consistent
  · intro v hv
    simp at hv
    rw [hC.run_input hv]

theorem tseitin_functional {C : Circuit} {ω : Assignment}
  (hC : C.WellFormed) (hω : (tseitin C).Sat ω) :
  C.outputs.map ω = C.eval ω := by
  apply hC.outputs_of_consistent
  rw [← sat_tseitin]
  exact hω

theorem tseitin_projSat_iff {C : Circuit} {ω : Assignment}
  (hC : C.WellFormed) :
  (tseitin C).ProjSat ω C.ioVars ↔ C.outputs.map ω = C.eval ω := by
  constructor <;> (
    unfold CNF.ProjSat
    intro h
  )
  · obtain ⟨ω', hω', h_eq⟩ := h
    simp [Circuit.ioVars, Set.EqOn, or_imp, forall_and] at h_eq
    obtain ⟨h_eq_in, h_eq_out⟩ := h_eq
    symm
    rw [← List.map_inj_left] at h_eq_out
    rw [← h_eq_out, tseitin_functional hC hω', hC.eval_congr]
    simp_all
  · unfold Circuit.eval at h
    use C.run ω
    constructor
    · rw [sat_tseitin]
      exact hC.run_consistent
    · intro v hv
      simp [Circuit.ioVars] at hv
      rcases hv with hv | hv
      · exact hC.run_input hv
      · rw [List.map_inj_left] at h
        symm
        exact h v hv

theorem mem_vars_tseitinGates {v : Variable}:
  ∀ {gl : GateList}, v ∈ (tseitinGates gl).vars →
                     ∃ v' g', (v', g') ∈ gl ∧ (v = v' ∨ v ∈ g'.args) := by
  intro gl
  induction gl with (
    intro h
    simp only [tseitinGates, CNF.vars_union, Finset.mem_union] at h
  )
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨v', g'⟩ := p
    rcases h with h | h
    · exact ⟨v', g', List.mem_cons.mpr (Or.inl rfl), Tseitin.vars_gateClauses h⟩
    · obtain ⟨v'', g'', hvg'', hv''⟩ := ih h
      exact ⟨v'', g'', List.mem_cons.mpr (Or.inr hvg''), hv''⟩

theorem vars_tseitin_subset_wires {C : Circuit} (hC : C.WellFormed) :
  (tseitin C).vars ⊆ C.wires := by
  unfold tseitin
  intro v hv
  rw [Circuit.mem_wires]
  unfold Circuit.IsWire
  obtain ⟨v', g', hvg', hv'⟩ := mem_vars_tseitinGates hv
  rcases hv' with rfl | hv'
  · exact Or.inr ⟨v, g', hvg', rfl⟩
  · unfold Circuit.WellFormed at hC
    obtain ⟨h_gwf, h_out⟩ := hC
    rcases h_gwf.arg_mem hvg' hv' with hv_in | h_gate
    · left
      simp_all
    · exact Or.inr h_gate

end LeanZKCEC
