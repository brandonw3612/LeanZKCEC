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
            rcases Finset.mem_insert.mp h_mem with h_mem | h_mem
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
      · rintro ⟨l, ⟨hl, h_lv⟩⟩ h_eq
        simp only [List.map_cons, List.cons.injEq] at h_eq
        obtain ⟨h_eq_h, h_eq_t⟩ := h_eq
        rcases List.mem_cons.mp hl with rfl | hl
        · exact h_neq.mp h_lv h_eq_h
        · exact ih'.mp ⟨l, ⟨hl, h_lv⟩⟩ h_eq_t
      · intro h_neq'
        by_cases h_eq_h : ω s = ω t
        · have h_neq_t : ss.map ω ≠ ts.map ω := by
            intro h_eq_t
            apply h_neq'
            simp [h_eq_h, h_eq_t]
          obtain ⟨l, ⟨hl, h_lv⟩⟩ := ih'.mpr h_neq_t
          refine ⟨l, ?_, h_lv⟩
          simp [hl]
        · refine ⟨⟨base + i, true⟩, ?_, h_neq.mpr h_eq_h⟩
          simp

namespace Miter

def base (spec impl : Circuit) : Variable :=
  freshVar (spec.wires ∪ impl.wires)

def ioGates (spec impl : Circuit) : GateList :=
  diffGates (base spec impl) 0 spec.outputs impl.outputs

def outClause (spec impl : Circuit) : Clause :=
  (outLiterals (base spec impl) 0 spec.outputs impl.outputs).toFinset

def Φio (spec impl : Circuit) : CNF :=
  tseitinGates (ioGates spec impl)

def Φpub (spec impl : Circuit) : CNF :=
  tseitin spec ∪ Φio spec impl ∪ {outClause spec impl}

def Φsec (impl : Circuit) : CNF :=
  tseitin impl

def Φmiter (spec impl : Circuit) : CNF :=
  Φpub spec impl ∪ Φsec impl

structure Compatible (spec impl : Circuit) : Prop where
  spec_wellformed : spec.WellFormed
  impl_wellformed : impl.WellFormed
  inputs_eq : spec.inputs = impl.inputs
  outputs_len : spec.outputs.length = impl.outputs.length
  shared : ∀ {v}, v ∈ spec.wires → v ∈ impl.wires → v ∈ spec.inputs

variable {spec impl : Circuit}

theorem unsat_of_equiv (h : Compatible spec impl) (h_eq : spec.Equiv impl) :
  CNF.Unsatisfiable (Φmiter spec impl) := by
  rw [CNF.unsat_iff]
  intro ω hω
  simp [Φmiter, CNF.sat_union, outClause, Clause.Sat, Φpub, Φio, Φsec] at hω
  obtain ⟨h_out, h_spec, h_io, h_impl⟩ := hω
  have h_spec_f := tseitin_functional h.spec_wellformed h_spec
  have h_impl_f := tseitin_functional h.impl_wellformed h_impl
  set iog := ioGates spec impl
  have h_io_sat : GatesConsistent ω iog := (sat_tseitinGates).mp h_io
  have h_neq := (outLiterals_sat_iff h_io_sat h.outputs_len).mp h_out
  apply h_neq
  rw [h_spec_f, h_impl_f, h_eq]

theorem base_add_not_mem {spec impl : Circuit} {k : ℕ} :
  base spec impl + k ∉ spec.wires ∪ impl.wires := by
  intro h_mem
  have h_mem := lt_freshVar h_mem
  unfold base freshVar at h_mem
  exact Nat.not_lt_of_le (Nat.le_add_right _ k) h_mem

theorem run_io_frame {spec impl : Circuit} {ω : Assignment} {v : Variable}
  (hv : v ∈ spec.wires ∪ impl.wires) :
  runGates (ioGates spec impl) ω v = ω v := by
  apply runGates_frame
  intro v' g' hvg' h_eq
  unfold ioGates at hvg'
  have ⟨k, hk, h_kv'⟩ := diffGates_out hvg'
  apply base_add_not_mem (spec := spec) (impl := impl) (k := k)
  rw [← h_kv', h_eq]
  exact hv

theorem impl_frame {ω : Assignment} {v : Variable}
  (hC : Compatible spec impl) (hv : v ∈ spec.wires) :
  impl.run ω v = ω v := by
  unfold Circuit.run
  apply runGates_frame
  intro v' g' hvg' h_eq
  apply hC.impl_wellformed.left.out_not_mem hvg'
  rw [h_eq, List.mem_toFinset, ← hC.inputs_eq]
  apply hC.shared hv
  rw [← h_eq, Circuit.mem_wires]
  exact Or.inr ⟨v', g', hvg', rfl⟩

def witness (spec impl : Circuit) (ω : Assignment) : Assignment :=
  runGates (ioGates spec impl) (impl.run (spec.run ω))

theorem witness_spec {ω : Assignment} {v : Variable}
  (hC : Compatible spec impl) (hv : v ∈ spec.wires) :
  witness spec impl ω v = spec.run ω v := by
  unfold witness
  rw [run_io_frame (spec := spec) (impl := impl) (Finset.mem_union_left _ hv),
      impl_frame hC hv]

theorem witness_impl {ω : Assignment} {v : Variable}
  (hv : v ∈ impl.wires) :
  witness spec impl ω v = impl.run (spec.run ω) v := by
  unfold witness
  rw [run_io_frame (spec := spec) (impl := impl) (Finset.mem_union_right _ hv)]

theorem witness_sat_spec {ω : Assignment}
  (hC : Compatible spec impl) :
  (tseitin spec).Sat (witness spec impl ω) := by
  set wn := witness spec impl ω
  have h_eq : Set.EqOn wn (spec.run ω) (tseitin spec).vars := by
    intro v hv
    apply witness_spec hC
    apply vars_tseitin_subset_wires hC.spec_wellformed
    simp_all
  rw [CNF.sat_congr h_eq]
  exact sat_tseitin.mpr hC.spec_wellformed.run_consistent

theorem witness_sat_impl {ω : Assignment}
  (hC : Compatible spec impl) :
  (tseitin impl).Sat (witness spec impl ω) := by
  set wn := witness spec impl ω
  have h_eq : Set.EqOn wn (impl.run (spec.run ω)) (tseitin impl).vars := by
    intro v hv
    apply witness_impl
    apply vars_tseitin_subset_wires hC.impl_wellformed
    simp_all
  rw [CNF.sat_congr h_eq]
  exact sat_tseitin.mpr hC.impl_wellformed.run_consistent

theorem ioGates_wellformed (hC : Compatible spec impl) :
  GatesWellFormed (spec.wires ∪ impl.wires) (ioGates spec impl) := by
  unfold ioGates
  apply diffGates_wellformed
  · intro v hv
    simp_all [hC.spec_wellformed.right]
  · intro v hv
    simp_all [hC.impl_wellformed.right]
  · intro k hk
    exact base_add_not_mem

theorem witness_io_consistent {ω : Assignment}
  (hC : Compatible spec impl) :
  GatesConsistent (witness spec impl ω) (ioGates spec impl) := by
  unfold witness
  exact (ioGates_wellformed hC).runGates_consistent

theorem equiv_of_unsat (hC : Compatible spec impl)
  (h_unsat : (Φmiter spec impl).Unsatisfiable) :
  spec.Equiv impl := by
  unfold Circuit.Equiv
  by_contra h_neq
  push Not at h_neq
  obtain ⟨ω, hω⟩ := h_neq
  set wn := witness spec impl ω
  set iog := ioGates spec impl
  have h_spec : spec.outputs.map wn = spec.eval ω := by
    unfold Circuit.eval
    rw [List.map_inj_left]
    intro v hv
    apply witness_spec hC
    rw [Circuit.mem_wires]
    exact hC.spec_wellformed.right hv
  have h_impl : impl.outputs.map wn = impl.eval (spec.run ω) := by
    unfold Circuit.eval
    rw [List.map_inj_left]
    intro v hv
    apply witness_impl
    rw [Circuit.mem_wires]
    exact hC.impl_wellformed.right hv
  have h_impl : impl.outputs.map wn = impl.eval ω := by
    rw [h_impl]
    apply hC.impl_wellformed.eval_congr
    intro v hv
    apply hC.spec_wellformed.run_input
    rw [hC.inputs_eq]
    exact hv
  have h_neq' : spec.outputs.map wn ≠ impl.outputs.map wn := by
    rw [h_spec, h_impl]
    exact hω
  have h_wn_io : GatesConsistent wn iog := witness_io_consistent hC
  have h_out : (outClause spec impl).Sat wn := by
    unfold iog ioGates at h_wn_io
    obtain ⟨l, hl, h_l_eq⟩ :=
      (outLiterals_sat_iff h_wn_io hC.outputs_len).mpr h_neq'
    unfold outClause Clause.Sat
    exact ⟨l, List.mem_toFinset.mpr hl, h_l_eq⟩
  have h_io : (Φio spec impl).Sat wn := by
    unfold Φio
    apply (sat_tseitinGates).mpr
    exact witness_io_consistent hC
  have h_sat : (Φmiter spec impl).Sat wn := by
    simp [Φmiter, CNF.sat_union, Φpub, Φsec]
    exact ⟨h_out, ⟨witness_sat_spec hC, ⟨h_io, witness_sat_impl hC⟩⟩⟩
  exact CNF.unsat_iff.mp h_unsat h_sat

theorem miter_correct (hC : Compatible spec impl) :
  (Φmiter spec impl).Unsatisfiable ↔ spec.Equiv impl :=
  ⟨equiv_of_unsat hC, unsat_of_equiv hC⟩

end Miter

end LeanZKCEC
