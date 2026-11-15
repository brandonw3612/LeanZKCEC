import LeanZKCEC.Logic.Vars

namespace LeanZKCEC

inductive Gate where
  | not (a : Variable)
  | and (a b : Variable)
  | or (a b : Variable)
  | xor (a b : Variable)
deriving DecidableEq, Repr

abbrev GateList := List (Variable × Gate)

namespace Gate

def args : Gate → VarList
  | not a => [a]
  | and a b => [a, b]
  | or a b => [a, b]
  | xor a b => [a, b]

def eval (ω : Assignment) : Gate → Bool
  | not a => !ω a
  | and a b => ω a && ω b
  | or a b => ω a || ω b
  | xor a b => ω a ^^ ω b

theorem eval_congr {σ τ : Assignment} {g : Gate}
  (h : ∀ {a}, a ∈ g.args → σ a = τ a) :
  g.eval σ = g.eval τ := by
  cases g <;> simp_all [args, eval]

end Gate

def runGates : GateList → Assignment → Assignment
  | [], ω => ω
  | (v, g) :: rest, ω => runGates rest (Function.update ω v (g.eval ω))

def GatesWellFormed : VarSet → GateList → Prop
  | _, [] => True
  | V, (v, g) :: rest =>
    (∀ {a}, a ∈ g.args → a ∈ V) ∧ v ∉ V ∧ GatesWellFormed (insert v V) rest

def GatesConsistent (ω : Assignment) (gl : GateList) : Prop :=
  ∀ {v g}, ⟨v, g⟩ ∈ gl → ω v = g.eval ω

theorem GatesConsistent.cons {ω : Assignment} {gl : GateList}
  {v : Variable} {g : Gate} :
    GatesConsistent ω (⟨v, g⟩ :: gl) ↔
    ω v = g.eval ω ∧ GatesConsistent ω gl := by
  unfold GatesConsistent
  simp [List.mem_cons, or_imp, forall_and]

theorem runGates_frame {v : Variable} :
  ∀ {gl : GateList} {ω : Assignment},
    (∀ {v' g'}, ⟨v', g'⟩ ∈ gl → v' ≠ v) → runGates gl ω v = ω v := by
  intro gl
  induction gl with intro ω hvg
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v', g'⟩ := p
    simp_all [runGates]
    by_cases hv' : v' = v
    · have hvg := hvg (Or.inl ⟨hv'.symm, rfl⟩)
      contradiction
    · have hvg : ∀ {v' g'}, ⟨v', g'⟩ ∈ rest → v' ≠ v := by
        intro v'' g'' hvg''
        apply hvg (Or.inr hvg'')
      simp [Function.update, ih hvg]
      intro hv''
      simp [hv''] at hv'

theorem GatesWellFormed.arg_mem : ∀ {gl : GateList} {V : VarSet},
  GatesWellFormed V gl →
    ∀ {v g}, (v, g) ∈ gl →
      ∀ {a}, a ∈ g.args → a ∈ V ∨
                          ∃ v' g', (v', g') ∈ gl ∧ v' = a := by
  intro gl
  induction gl with intro V h_wf v' g' hvg' a ha
  | nil =>
    simp at hvg'
  | cons p rest ih =>
    obtain ⟨v, g⟩ := p
    unfold GatesWellFormed at h_wf
    obtain ⟨h_args, hv, h_rest⟩ := h_wf
    rw [List.mem_cons] at hvg'
    rcases hvg' with ⟨rfl, rfl⟩ | hvg'
    · exact Or.inl (h_args ha)
    · rcases ih h_rest hvg' ha with h | ⟨v'', g'', hvg'', hv''⟩
      · rw [Finset.mem_insert] at h
        rcases h with h_eq | h_in
        · exact Or.inr ⟨v, g, List.mem_cons.mpr (Or.inl rfl), h_eq.symm⟩
        · exact Or.inl h_in
      · exact Or.inr ⟨v'', g'', List.mem_cons.mpr (Or.inr hvg''), hv''⟩

theorem GatesWellFormed.out_not_mem :
  ∀ {gl : GateList} {V : VarSet},
    GatesWellFormed V gl → ∀ {v g}, ⟨v, g⟩ ∈ gl → v ∉ V := by
  intro gl
  induction gl with intro V h_wf v g hvg
  | nil => simp at hvg
  | cons q rest ih =>
    unfold GatesWellFormed at h_wf
    obtain ⟨h_args, hv, h_rest⟩ := h_wf
    rw [List.mem_cons] at hvg
    rcases hvg with rfl | hp
    · exact hv
    · intro hp'
      apply ih h_rest hp
      exact Finset.mem_insert_of_mem hp'

theorem GatesWellFormed.runGates_consistent :
  ∀ {gl : GateList} {V : VarSet} {ω : Assignment},
    GatesWellFormed V gl → GatesConsistent (runGates gl ω) gl := by
    intro gl
    induction gl with intro V ω h_wf
    | nil =>
      intro v g hvg
      simp at hvg
    | cons p rest ih =>
      obtain ⟨v, g⟩ := p
      unfold GatesWellFormed at h_wf
      obtain ⟨h_args, hv, h_rest⟩ := h_wf
      unfold GatesConsistent
      intro v' g' hvg'
      simp [runGates]
      rw [List.mem_cons] at hvg'
      rcases hvg' with ⟨rfl, rfl⟩ | hvg'
      · have hl : runGates rest (Function.update ω v (g.eval ω)) v
                = g.eval ω := by
          rw [runGates_frame]
          · simp
          · intro v'' g'' hvg'' hv''
            apply h_rest.out_not_mem hvg''
            simp [hv'']
        have hr : g.eval (runGates rest (Function.update ω v (g.eval ω)))
                = g.eval ω := by
          apply Gate.eval_congr
          intro v' hv'
          rw [runGates_frame]
          · rw [Function.update_apply, ite_eq_right]
            intro h_eq
            subst v'
            exact hv (h_args hv')
          · intro v'' g'' hvg'' hv''
            apply h_rest.out_not_mem hvg''
            rw [hv'']
            exact Finset.mem_insert_of_mem (h_args hv')
        rw [hl, hr]
      · exact ih h_rest hvg'

theorem GatesWellFormed.consistent_unique :
  ∀ {gl : GateList} {V : VarSet} {σ τ : Assignment},
    GatesWellFormed V gl → GatesConsistent σ gl → GatesConsistent τ gl →
    (∀ {v}, v ∈ V → σ v = τ v) → ∀ {v g}, ⟨v, g⟩ ∈ gl → σ v = τ v := by
    intro gl
    induction gl with intro V σ τ h_wf hσ hτ h_eq
    | nil => simp_all
    | cons p rest ih =>
      obtain ⟨v, g⟩ := p
      unfold GatesWellFormed at h_wf
      obtain ⟨h_args, hv, h_rest⟩ := h_wf
      have h_eq' : σ v = τ v := by
        have hσ := hσ (List.mem_cons.mpr (Or.inl rfl))
        have hτ := hτ (List.mem_cons.mpr (Or.inl rfl))
        rw [hσ, hτ]
        apply Gate.eval_congr
        intro v hv
        exact h_eq (h_args hv)
      have hσ : GatesConsistent σ rest := (GatesConsistent.cons.mp hσ).right
      have hτ : GatesConsistent τ rest := (GatesConsistent.cons.mp hτ).right
      intro v' g' hvg'
      rw [List.mem_cons] at hvg'
      rcases hvg' with ⟨rfl, rfl⟩ | hvg'
      · exact h_eq'
      · apply ih h_rest hσ hτ ?_ hvg'
        intro v hv
        rw [Finset.mem_insert] at hv
        rcases hv with rfl | hv
        · exact h_eq'
        · exact h_eq hv

structure Circuit where
  inputs : VarList
  gates : GateList
  outputs : VarList
deriving Repr

namespace Circuit

def run (C : Circuit) (ω : Assignment) : Assignment :=
  runGates C.gates ω

def eval (C : Circuit) (ω : Assignment) : List Bool :=
  C.outputs.map (C.run ω)

def IsWire (C : Circuit) (v : Variable) : Prop :=
  v ∈ C.inputs ∨ ∃ v' g', ⟨v', g'⟩ ∈ C.gates ∧ v' = v

def wires (C : Circuit) : VarSet :=
  C.inputs.toFinset ∪ (C.gates.map Prod.fst).toFinset

def ioVars (C : Circuit) : VarSet :=
  C.inputs.toFinset ∪ C.outputs.toFinset

@[simp]
theorem mem_wires {C : Circuit} {v : Variable} :
  v ∈ C.wires ↔ C.IsWire v := by
  simp [wires, IsWire]

def WellFormed (C : Circuit) : Prop :=
  GatesWellFormed C.inputs.toFinset C.gates ∧
  ∀ {v}, v ∈ C.outputs → C.IsWire v

def Consistent (C : Circuit) (ω : Assignment) : Prop :=
  GatesConsistent ω C.gates

def Equiv (C C' : Circuit) : Prop :=
  ∀ {ω}, C.eval ω = C'.eval ω

theorem Equiv.refl (C : Circuit) : C.Equiv C := by
  simp_all [Equiv]

theorem Equiv.symm {C C' : Circuit} : C.Equiv C' → C'.Equiv C := by
  simp_all [Equiv]

theorem Equiv.trans {C C' C'' : Circuit} :
  C.Equiv C' → C'.Equiv C'' → C.Equiv C'' := by
  simp_all [Equiv]

theorem WellFormed.run_input {C : Circuit} {v : Variable} {ω : Assignment}
  (hC : C.WellFormed) (hv : v ∈ C.inputs) :
  C.run ω v = ω v := by
  unfold run
  unfold WellFormed at hC
  obtain ⟨h_gwf, h_out⟩ := hC
  apply runGates_frame
  intro v g hvg h_eq
  apply h_gwf.out_not_mem hvg
  simp_all

theorem WellFormed.run_consistent {C : Circuit} {ω : Assignment}
  (hC : C.WellFormed) :
  C.Consistent (C.run ω) := by
  unfold Consistent run
  unfold WellFormed at hC
  obtain ⟨h_gwf, h_out⟩ := hC
  exact h_gwf.runGates_consistent

theorem WellFormed.total {C : Circuit} (τ : Assignment)
  (hC : C.WellFormed) :
  ∃ σ, C.Consistent σ ∧
       ∀ {v}, v ∈ C.inputs → σ v = τ v := by
  refine ⟨C.run τ, ⟨hC.run_consistent, ?_⟩⟩
  intro v hv
  exact hC.run_input hv

theorem WellFormed.consistent_eq_run
  {C : Circuit} {ω : Assignment} {v : Variable}
  (hC : C.WellFormed) (hω : C.Consistent ω) (hv : C.IsWire v) :
  C.run ω v = ω v := by
  rcases hv with hv | ⟨v, g, hvg, rfl⟩
  · exact hC.run_input hv
  · have ⟨h_gwf, h_out⟩ := hC
    have h_run : GatesConsistent (C.run ω) C.gates :=
      GatesWellFormed.runGates_consistent h_gwf
    apply h_gwf.consistent_unique h_run hω ?_ hvg
    intro v hv
    apply hC.run_input
    simp_all

theorem WellFormed.outputs_of_consistent {C : Circuit} {ω : Assignment}
  (hC : C.WellFormed) (hω : C.Consistent ω) :
  C.outputs.map ω = C.eval ω := by
  unfold eval
  rw [List.map_inj_left]
  intro v hv
  rw [hC.consistent_eq_run hω (hC.2 hv)]

theorem WellFormed.run_congr {C : Circuit} {σ τ : Assignment} {v : Variable}
  (hC : C.WellFormed) (h_eq : ∀ {v}, v ∈ C.inputs → σ v = τ v)
  (hv : C.IsWire v) :
  C.run σ v = C.run τ v := by
  rcases hv with hv | ⟨v, g, hvg, rfl⟩
  · simp [hC.run_input hv]
    exact h_eq hv
  · have ⟨h_gwf, h_out⟩ := hC
    apply h_gwf.consistent_unique (hC.run_consistent) (hC.run_consistent) ?_ hvg
    intro v hv
    simp_all [hC.run_input]

theorem WellFormed.eval_congr {C : Circuit} {σ τ : Assignment}
  (hC : C.WellFormed) (h_eq : ∀ {v}, v ∈ C.inputs → σ v = τ v) :
  C.eval σ = C.eval τ := by
  unfold Circuit.eval
  rw [List.map_inj_left]
  intro v hv
  have ⟨h_gwf, h_out⟩ := hC
  exact hC.run_congr h_eq (h_out hv)

end Circuit

end LeanZKCEC
