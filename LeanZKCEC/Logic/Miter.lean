import LeanZKCEC.Logic.Tseitin

namespace LeanZKCEC

def diffGates (base : Variable) : ℕ → VarList → VarList → GateList
  | i, s :: ss, t :: ts =>
    (base + i, Gate.xor s t) :: diffGates base (i + 1) ss ts
  | _, _, _ => []

def outLiterals (base : Variable) : ℕ → VarList → VarList → LitList
  | i, _ :: ss, _ :: ts =>
    ⟨base + i, true⟩ :: outLiterals base (i + 1) ss ts
  | _, _, _ => []

theorem diffGates_out {base : Variable} :
  ∀ {ss ts : VarList} {i : ℕ} {v g}, ⟨v, g⟩ ∈ diffGates base i ss ts →
    ∃ k, i ≤ k ∧ v = base + k := by
    intro ss
    induction ss with intro ts i v g hvg
    | nil => simp [diffGates] at hvg
    | cons s ss ih =>
      cases ts with
      | nil => simp [diffGates] at hvg
      | cons t ts =>
        simp [diffGates, List.mem_cons] at hvg
        rcases hvg with ⟨rfl, rfl⟩ | hvg
        · exact ⟨i, le_rfl, rfl⟩
        · obtain ⟨k, hk, hvk⟩ := ih hvg
          exact ⟨k, (by omega), hvk⟩

theorem diffGates_wellformed {base : Variable} :
  ∀ {ss ts : VarList} {i : ℕ} {V : VarSet},
    (∀ {v}, v ∈ ss → v ∈ V) →
    (∀ {v}, v ∈ ts → v ∈ V) →
    (∀ {k}, i ≤ k → base + k ∉ V) →
    GatesWellFormed V (diffGates base i ss ts) := by
  intro ss
  induction ss with intro ts i V hs ht hk
  | nil => simp [diffGates, GatesWellFormed]
  | cons s ss ih =>
    cases ts with simp [diffGates, GatesWellFormed]
    | cons t ts =>
      constructor
      · intro a ha
        simp [Gate.args] at ha
        rcases ha with rfl | rfl <;> simp_all
      · constructor
        · exact hk le_rfl
        · apply ih
          · intro v hv
            apply Finset.mem_insert_of_mem
            tauto
          · intro v hv
            apply Finset.mem_insert_of_mem
            tauto
          · intro k hk' h_mem
            rw [Finset.mem_insert] at h_mem
            rcases h_mem with h_mem | h_mem
            · simp_all
              omega
            · exact hk (by omega) h_mem

theorem outLiterals_sat_iff {ω : Assignment} {base : Variable} :
  ∀ {ss ts : VarList} {i : ℕ},
    GatesConsistent ω (diffGates base i ss ts) →
    ss.length = ts.length →
    ((∃ l ∈ outLiterals base i ss ts, l.eval ω) ↔
     ss.map ω ≠ ts.map ω) := by
  intro ss
  induction ss with intro ts i h_gc h_len
  | nil =>
    cases ts with simp_all [outLiterals] ;
  | cons s ss ih =>
    cases ts with simp at h_len
    | cons t ts =>
      unfold GatesConsistent at h_gc
      simp [diffGates] at h_gc
      set g := Gate.xor s t
      have h_gc' := h_gc (v := base + i) (g := g)
      simp at h_gc'
      have h_rest : GatesConsistent ω (diffGates base (i + 1) ss ts) := by
        intro v g hvg
        apply h_gc
        simp [hvg]
      have ih' := ih h_rest h_len
      have h_neq : Literal.eval ω ⟨base + i, true⟩ ↔ ω s ≠ ω t := by
        cases hs : ω s <;> cases ht : ω t <;>
        simp [Literal.eval, g, Gate.eval, h_gc', hs, ht]
      unfold outLiterals
      constructor
      · rintro ⟨l, hl, h_l_eval⟩ h_eq
        simp only [List.map_cons, List.cons.injEq] at h_eq
        obtain ⟨h_eq_h, h_eq_t⟩ := h_eq
        rw [List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact h_neq.mp h_l_eval h_eq_h
        · exact ih'.mp ⟨l, hl, h_l_eval⟩ h_eq_t
      · intro h_neq'
        by_cases h_eq_h : ω s = ω t
        · have h_neq_t : ss.map ω ≠ ts.map ω := by
            intro h_eq_t
            apply h_neq'
            simp [h_eq_h, h_eq_t]
          rw [← ih'] at h_neq_t
          obtain ⟨l, hl, h_l_eval⟩ := h_neq_t
          refine ⟨l, ?_, h_l_eval⟩
          simp [hl]
        · rw [← ne_eq, ← h_neq] at h_eq_h
          refine ⟨⟨base + i, true⟩, ?_, h_eq_h⟩
          simp

namespace Miter

structure Interface where
  spec : Circuit
  implOutputs : VarList

namespace Interface

def ioVars (I : Interface) : VarSet :=
  I.spec.inputs.toFinset ∪ I.implOutputs.toFinset

def knownVars (I : Interface) : VarSet :=
  I.spec.wires ∪ I.implOutputs.toFinset

def base (I : Interface) : Variable :=
  freshVar (I.knownVars)

def ioGates (I : Interface) : GateList :=
  diffGates (I.base) 0 I.spec.outputs I.implOutputs

def outClause (I : Interface) : Clause :=
  (outLiterals I.base 0 I.spec.outputs I.implOutputs).toFinset

def Φio (I : Interface) : CNF :=
  tseitinGates (I.ioGates)

def Φpub (I : Interface) : CNF :=
  tseitin I.spec ∪ I.Φio ∪ {I.outClause}

def witness (I : Interface) (ω : Assignment) : Assignment :=
  runGates (I.ioGates) (I.spec.run ω)

structure WellFormed (I : Interface) : Prop where
  spec_wellformed : I.spec.WellFormed
  outputs_len : I.spec.outputs.length = I.implOutputs.length
  outputs_fresh : ∀ {v},
                    v ∈ I.implOutputs → v ∈ I.spec.wires → v ∈ I.spec.inputs

variable {I : Interface}

theorem ne_of_sat_pub {ω : Assignment}
  (hI : I.WellFormed) (hω : I.Φpub.Sat ω) :
  I.implOutputs.map ω ≠ I.spec.eval ω := by
  simp [Φpub, CNF.sat_union] at hω
  obtain ⟨h_out, h_spec, h_io⟩ := hω
  have h_io_cons : GatesConsistent ω I.ioGates := sat_tseitinGates.mp h_io
  unfold ioGates at h_io_cons
  set outLits := outLiterals I.base 0 I.spec.outputs I.implOutputs
  have h_ex : ∃ l ∈ outLits, l.eval ω := by
    unfold outClause Clause.Sat at h_out
    obtain ⟨l, hl, h_l_eval⟩ := h_out
    rw [List.mem_toFinset] at hl
    exact ⟨l, hl, h_l_eval⟩
  rw [outLiterals_sat_iff h_io_cons hI.outputs_len,
      tseitin_functional hI.spec_wellformed h_spec] at h_ex
  exact h_ex.symm

theorem base_add_not_mem {k : ℕ} :
  I.base + k ∉ I.knownVars := by
  intro h_mem
  have h_mem := lt_freshVar h_mem
  unfold base freshVar at h_mem
  exact Nat.not_lt_of_le (Nat.le_add_right _ k) h_mem

theorem ioGates_frame {ω : Assignment} {v : Variable}
  (hv : v ∈ I.knownVars) :
  runGates I.ioGates ω v = ω v := by
  apply runGates_frame
  intro v' g' hvg' h_eq
  unfold ioGates at hvg'
  have ⟨k, hk, h_kv'⟩ := diffGates_out hvg'
  apply base_add_not_mem (I := I) (k := k)
  rw [← h_kv', h_eq]
  exact hv

theorem spec_run_implOutput {ω : Assignment} {v : Variable}
  (hI : I.WellFormed) (hv : v ∈ I.implOutputs) :
  I.spec.run ω v = ω v := by
  by_cases hv' : v ∈ I.spec.inputs
  · exact hI.spec_wellformed.run_input hv'
  · unfold Circuit.run
    apply runGates_frame
    intro v' g' hvg' h_eq
    apply hv'
    apply hI.outputs_fresh hv
    rw [← h_eq, Circuit.mem_wires]
    exact Or.inr ⟨v', g', hvg', rfl⟩

theorem ioGates_wellformed
  (hI : I.WellFormed) :
  GatesWellFormed I.knownVars I.ioGates := by
  unfold ioGates
  apply diffGates_wellformed
  · intro v hv
    simp_all [knownVars, hI.spec_wellformed.right]
  · intro v hv
    simp_all [knownVars]
  · intro k hk
    exact base_add_not_mem

theorem witness_eqOn_io {ω : Assignment}
  (hI : I.WellFormed) :
  Set.EqOn (I.witness ω) ω I.ioVars := by
  intro v hv
  simp [ioVars] at hv
  unfold witness
  rcases hv with hv | hv
  · have h_known : v ∈ I.knownVars := by
      unfold knownVars
      apply Finset.mem_union_left
      apply Circuit.mem_wires.mpr
      simp [Circuit.IsWire, hv]
    rw [ioGates_frame h_known, hI.spec_wellformed.run_input hv]
  · have h_known : v ∈ I.knownVars := by
      unfold knownVars
      apply Finset.mem_union_right
      simp [hv]
    rw [ioGates_frame h_known, spec_run_implOutput hI hv]

theorem witness_sat_pub {ω : Assignment}
  (hI : I.WellFormed) (h_neq : I.implOutputs.map ω ≠ I.spec.eval ω) :
  I.Φpub.Sat (I.witness ω) := by
  have h_eq : Set.EqOn (I.witness ω) (I.spec.run ω) (tseitin I.spec).vars := by
      intro v hv
      unfold witness
      apply ioGates_frame
      apply Finset.mem_union_left
      apply vars_tseitin_subset_wires hI.spec_wellformed
      simp_all
  have h_spec : (tseitin I.spec).Sat (I.witness ω) := by
    rw [CNF.sat_congr h_eq, sat_tseitin]
    exact hI.spec_wellformed.run_consistent
  have h_io_cons : GatesConsistent (I.witness ω) I.ioGates := by
    unfold witness
    exact (ioGates_wellformed hI).runGates_consistent
  have h_spec_out : I.spec.outputs.map (I.witness ω) = I.spec.eval ω := by
    unfold Circuit.eval
    rw [List.map_inj_left]
    intro v hv
    unfold witness
    apply ioGates_frame
    simp_all [knownVars, hI.spec_wellformed.right]
  have h_impl_out : I.implOutputs.map (I.witness ω) = I.implOutputs.map ω := by
    unfold witness
    rw [List.map_inj_left]
    intro v hv
    apply witness_eqOn_io hI
    simp_all [ioVars]
  have h_neq' : I.spec.outputs.map (I.witness ω) ≠
                I.implOutputs.map (I.witness ω) := by
    rw [h_spec_out, h_impl_out]
    exact h_neq.symm
  have h_out : I.outClause.Sat (I.witness ω) := by
    unfold ioGates at h_io_cons
    rw [← outLiterals_sat_iff h_io_cons hI.outputs_len] at h_neq'
    obtain ⟨l, hl, h_l_eval⟩ := h_neq'
    rw [← List.mem_toFinset] at hl
    unfold outClause Clause.Sat
    exact ⟨l, hl, h_l_eval⟩
  simp [Φpub, CNF.sat_union, Φio]
  rw [← sat_tseitinGates] at h_io_cons
  exact ⟨h_out, h_spec, h_io_cons⟩

theorem outputs_of_unsat {Φ : CNF} {ω : Assignment}
  (hI : I.WellFormed) (h_vars : Φ.vars ∩ I.Φpub.vars ⊆ I.ioVars)
  (hω : Φ.Sat ω) (h_unsat : (I.Φpub ∪ Φ).Unsatisfiable) :
  I.implOutputs.map ω = I.spec.eval ω := by
  by_contra h_neq
  have h_pub : I.Φpub.Sat (I.witness ω) := witness_sat_pub hI h_neq
  have h_eq : Set.EqOn (I.witness ω) ω (I.Φpub.vars ∩ Φ.vars) := by
    intro v hv
    rw [← Finset.coe_inter, Finset.mem_coe, Finset.inter_comm] at hv
    apply witness_eqOn_io hI
    rw [Finset.mem_coe]
    exact Finset.mem_of_subset h_vars hv
  rw [CNF.unsat_iff] at h_unsat
  apply h_unsat (ω := (I.witness ω).glue ω I.Φpub.vars)
  exact CNF.sat_union_glue h_pub hω h_eq

theorem unsat_of_outputs {Φ : CNF}
  (hI : I.WellFormed)
  (h : ∀ {ω}, Φ.Sat ω → I.implOutputs.map ω = I.spec.eval ω) :
  (I.Φpub ∪ Φ).Unsatisfiable := by
  rw [CNF.unsat_iff]
  intro ω hω
  rw [CNF.sat_union] at hω
  obtain ⟨h_sat_pub, h_sat_Φ⟩ := hω
  exact ne_of_sat_pub hI h_sat_pub (h h_sat_Φ)

theorem unsat_iff_outputs {Φ : CNF}
  (hI : I.WellFormed) (h_vars : Φ.vars ∩ I.Φpub.vars ⊆ I.ioVars) :
  (I.Φpub ∪ Φ).Unsatisfiable ↔
  ∀ {ω}, Φ.Sat ω → I.implOutputs.map ω = I.spec.eval ω := by
  constructor
  · intro h_unsat ω hω
    exact outputs_of_unsat hI h_vars hω h_unsat
  · intro h_eq
    exact unsat_of_outputs hI h_eq

def ofCircuits (spec impl : Circuit) : Interface := ⟨spec, impl.outputs⟩

@[simp]
theorem ofCircuits_spec {spec impl : Circuit} :
  (ofCircuits spec impl).spec = spec := rfl

@[simp]
theorem ofCircuits_implOutputs {spec impl : Circuit} :
  (ofCircuits spec impl).implOutputs = impl.outputs := rfl

end Interface

def Φpub (spec impl : Circuit) : CNF :=
  (Interface.ofCircuits spec impl).Φpub

def Φsec (impl : Circuit) : CNF :=
  tseitin impl

def Φmiter (spec impl : Circuit) : CNF :=
  Φpub spec impl ∪ Φsec impl

structure Compatible (spec impl : Circuit) : Prop where
  interface_wellformed : (Interface.ofCircuits spec impl).WellFormed
  impl_wellformed : impl.WellFormed
  inputs_eq : spec.inputs = impl.inputs
  isolated : (tseitin impl).vars ∩ (Interface.ofCircuits spec impl).Φpub.vars ⊆
             (Interface.ofCircuits spec impl).ioVars

variable {spec impl : Circuit}

theorem unsat_of_equiv (hC : Compatible spec impl) (h_eq : spec.Equiv impl) :
  (Φmiter spec impl).Unsatisfiable := by
  unfold Φmiter Φpub Φsec
  rw [Interface.unsat_iff_outputs hC.interface_wellformed hC.isolated]
  intro ω hω
  simp [tseitin_functional hC.impl_wellformed hω]
  exact h_eq.symm

theorem equiv_of_unsat (hC : Compatible spec impl)
  (h_unsat : (Φmiter spec impl).Unsatisfiable) :
  spec.Equiv impl := by
  unfold Φmiter Φpub Φsec at h_unsat
  simp [Interface.unsat_iff_outputs hC.interface_wellformed hC.isolated] at h_unsat
  unfold Circuit.Equiv
  intro ω
  have h_sat_run : (tseitin impl).Sat (impl.run ω) :=
    sat_tseitin.mpr hC.impl_wellformed.run_consistent
  have h_out := h_unsat h_sat_run
  have h_in : ∀ {v}, v ∈ spec.inputs → impl.run ω v = ω v := by
    intro v hv
    rw [hC.inputs_eq] at hv
    exact hC.impl_wellformed.run_input hv
  have h := hC.interface_wellformed.spec_wellformed.eval_congr h_in
  simp at h h_out
  rw [← h]
  exact h_out.symm

theorem miter_correct (hC : Compatible spec impl) :
  (Φmiter spec impl).Unsatisfiable ↔ spec.Equiv impl := by
  exact ⟨equiv_of_unsat hC, unsat_of_equiv hC⟩

end Miter

end LeanZKCEC
