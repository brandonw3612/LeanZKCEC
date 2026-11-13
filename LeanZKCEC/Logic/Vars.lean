import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union

import LeanZKCEC.Logic.Basic

namespace LeanZKCEC

theorem Literal.eval_congr {σ τ : Assignment} {l : Literal}
  (h : σ l.var = τ l.var) :
  l.eval σ = l.eval τ := by
  simp [Literal.eval, h]

namespace Clause

def vars (c : Clause) : VarSet := c.image Literal.var

@[simp]
theorem mem_vars {c : Clause} {v : Variable} :
  v ∈ c.vars ↔ ∃ l ∈ c, l.var = v := by
  simp [vars]

theorem vars_mem_vars {c : Clause} {l : Literal} (h : l ∈ c) :
  l.var ∈ c.vars :=
  mem_vars.2 ⟨l, h, rfl⟩

@[simp]
theorem vars_empty : Clause.vars ∅ = ∅ := by
  simp [vars]

@[simp]
theorem vars_singleton {l : Literal} :
  Clause.vars {l} = {l.var} := by
  simp [vars]

theorem vars_union {c c' : Clause} :
  (c ∪ c').vars = c.vars ∪ c'.vars := by
  simp [vars, Finset.image_union]

theorem vars_mono {c c' : Clause} (h : c ⊆ c') :
  c.vars ⊆ c'.vars :=
  Finset.image_subset_image h

theorem sat_congr {σ τ : Assignment} {c : Clause} (h : Set.EqOn σ τ c.vars) :
  Sat σ c ↔ Sat τ c := by
  unfold Sat
  simp [Set.EqOn] at h
  constructor <;> (
    rintro ⟨l, hl, hv⟩
    use l
    simp_all [← hv, Literal.eval_congr (h l hl)]
  )

end Clause

namespace CNF

def vars (Φ : CNF) : VarSet := Φ.biUnion Clause.vars

@[simp]
theorem mem_vars {Φ : CNF} {v : Variable} :
  v ∈ Φ.vars ↔ ∃ c ∈ Φ, v ∈ c.vars := by
  simp [vars]

theorem clause_vars_subset {Φ : CNF} {c : Clause} (h : c ∈ Φ) :
  c.vars ⊆ Φ.vars := by
  intro v hv
  exact mem_vars.2 ⟨c, h, hv⟩

@[simp]
theorem vars_empty : CNF.vars ∅ = ∅ := by
  simp [vars]

theorem vars_union {Φ Ψ : CNF} :
  (Φ ∪ Ψ).vars = Φ.vars ∪ Ψ.vars := by
  ext v
  simp [vars, or_and_right, exists_or]

theorem vars_insert {c : Clause} {Φ : CNF} :
  (insert c Φ).vars = c.vars ∪ Φ.vars := by
  simp [vars]

theorem vars_mono {Φ Ψ : CNF} (h : Φ ⊆ Ψ) :
  Φ.vars ⊆ Ψ.vars := by
  intro v hv
  simp_all [mem_vars]
  obtain ⟨c, hc, hv⟩ := hv
  exact ⟨c, h hc, hv⟩

theorem sat_congr {σ τ : Assignment} {Φ : CNF} (h : Set.EqOn σ τ Φ.vars) :
  Sat σ Φ ↔ Sat τ Φ := by
  unfold Sat
  have h' : ∀ {c}, c ∈ Φ → (c.Sat σ ↔ c.Sat τ) := by
    intro c hc
    apply Clause.sat_congr
    exact h.mono (clause_vars_subset hc)
  simp_all

end CNF

namespace Assignment

def glue (σ τ : Assignment) (S : VarSet) : Assignment :=
  fun v => if v ∈ S then σ v else τ v

theorem glue_eqOn_left {σ τ : Assignment} {S : VarSet} :
  Set.EqOn (glue σ τ S) σ S := by
  intro v hv
  simp [glue, Finset.mem_coe.mp hv]

theorem glue_eqOn_right {σ τ : Assignment} {S T : VarSet}
  (h : Set.EqOn σ τ (S ∩ T)) :
  Set.EqOn (glue σ τ S) τ T := by
  intro v hv
  simp [glue]
  intro hS
  apply h
  simp_all

end Assignment

namespace CNF

theorem sat_union_glue {σ τ : Assignment} {Φ Ψ : CNF}
  (h₁ : Sat σ Φ) (h₂ : Sat τ Ψ) (h : Set.EqOn σ τ (Φ.vars ∩ Ψ.vars)) :
  Sat (Assignment.glue σ τ Φ.vars) (Φ ∪ Ψ) := by
  rw [sat_union]
  constructor
  · exact (sat_congr Assignment.glue_eqOn_left).2 h₁
  · exact (sat_congr (Assignment.glue_eqOn_right h)).2 h₂

theorem satisfiable_union_of_agree {Φ Ψ : CNF} {σ τ : Assignment}
  (h₁ : Sat σ Φ) (h₂ : Sat τ Ψ) (h : Set.EqOn σ τ (Φ.vars ∩ Ψ.vars)) :
  Satisfiable (Φ ∪ Ψ) := by
  use Assignment.glue σ τ Φ.vars
  exact sat_union_glue h₁ h₂ h

def ProjSat (Φ : CNF) (ω : Assignment) (S : VarSet) : Prop :=
  ∃ ω', Sat ω' Φ ∧ Set.EqOn ω' ω S

theorem projSat_of_sat {Φ : CNF} {ω : Assignment} {S : VarSet}
  (h : Sat ω Φ) :
  ProjSat Φ ω S := by
  unfold ProjSat
  exact ⟨ω, h, Set.eqOn_refl ω S⟩

theorem ProjSat.congr {Φ : CNF} {σ τ : Assignment} {S : VarSet}
  (h : ProjSat Φ σ S) (h_eq : Set.EqOn σ τ S) :
  ProjSat Φ τ S := by
  unfold ProjSat at *
  obtain ⟨ω'', hω'', h_eq''⟩ := h
  exact ⟨ω'', hω'', h_eq''.trans h_eq⟩

end CNF

def Consistent (S : LitSet) : Prop := ∀ {l}, l ∈ S → l.neg ∉ S

def toAssignment (S : LitSet) : Assignment :=
  fun v => decide (Literal.ofVar v ∈ S)

theorem eval_toAssignment {S : LitSet} {l : Literal}
  (hS : Consistent S) (hl : l ∈ S) :
  l.eval (toAssignment S) := by
  unfold Consistent at hS
  obtain ⟨v, p⟩ := l
  cases p with simp [Literal.eval, toAssignment]
  | true => simp_all [Literal.ofVar]
  | false =>
    have hS := hS hl
    simp [Literal.neg] at hS
    exact hS

theorem CNF.sat_toAssignment {S : LitSet} {Φ : CNF}
  (hS : Consistent S) (h_hit : ∀ {c}, c ∈ Φ → ∃ l ∈ c, l ∈ S) :
  Φ.Sat (toAssignment S) := by
  intro c hc
  obtain ⟨l, hlc, hls⟩ := h_hit hc
  unfold Clause.Sat
  exact ⟨l, hlc, eval_toAssignment hS hls⟩

theorem CNF.satisfiable_of_hitting {S : LitSet} {Φ : CNF}
  (hS : Consistent S) (h_hit : ∀ {c}, c ∈ Φ → ∃ l ∈ c, l ∈ S) :
  Φ.Satisfiable := by
  unfold CNF.Satisfiable
  exact ⟨_, sat_toAssignment hS h_hit⟩

def trueLiterals (ω : Assignment) (V : VarSet) : LitSet :=
  V.image fun v => ⟨v, ω v⟩

theorem consistent_trueLiterals (ω : Assignment) (V : VarSet) :
  Consistent (trueLiterals ω V) := by
  unfold Consistent trueLiterals
  intro l hl
  simp_all [Finset.mem_image]
  obtain ⟨u, hu, rfl⟩ := hl
  simp_all [Literal.neg]

theorem mem_trueLiterals {ω : Assignment} {V : VarSet} {l : Literal}
  (hV : l.var ∈ V) (he : l.eval ω) :
  l ∈ trueLiterals ω V := by
  unfold trueLiterals
  rw [Finset.mem_image]
  refine ⟨l.var, hV, ?_⟩
  obtain ⟨v, p⟩ := l
  cases p <;> simp_all [Literal.eval]

theorem hit_trueLiterals {ω : Assignment} {Φ : CNF} {V : VarSet}
  (h_sat : Φ.Sat ω) (hV : Φ.vars ⊆ V) :
  ∀ {c}, c ∈ Φ → ∃ l ∈ c, l ∈ trueLiterals ω V := by
  intro c hc
  obtain ⟨l, hl, he⟩ := h_sat hc
  refine ⟨l, hl, ?_⟩
  apply mem_trueLiterals
  · apply hV
    apply CNF.mem_vars.2
    exact ⟨c, hc, Clause.vars_mem_vars hl⟩
  · exact he

def freshVar (S : VarSet) : Variable := S.sup id + 1

theorem lt_freshVar {S : VarSet} :
  ∀ {v}, v ∈ S → v < freshVar S := by
  intro v hv
  unfold freshVar
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)

theorem freshVar_not_mem {S : VarSet} :
  freshVar S ∉ S := by
  intro h
  exact lt_irrefl (freshVar S) (lt_freshVar h)

end LeanZKCEC
