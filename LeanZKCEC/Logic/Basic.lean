import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

namespace LeanZKCEC

abbrev Variable := ℕ

abbrev VarSet := Finset Variable

abbrev VarList := List Variable

abbrev Assignment := Variable → Bool

structure Literal where
  var : Variable
  pos : Bool
deriving DecidableEq, Repr, Hashable

abbrev LitSet := Finset Literal

abbrev LitList := List Literal

namespace Literal

def ofVar (v : Variable) : Literal := ⟨v, true⟩

def neg (l : Literal) : Literal := ⟨l.var, !l.pos⟩

@[simp]
theorem neg_var {l : Literal} : l.neg.var = l.var := rfl

@[simp]
theorem neg_pos {l : Literal} : l.neg.pos = !l.pos := rfl

@[simp]
theorem neg_neg {l : Literal} : l.neg.neg = l := by
  cases l
  simp [neg]

theorem neg_injective : neg.Injective := by
  intro l₁ l₂ h_neg
  cases l₁
  cases l₂
  simp_all [neg]

theorem neg_ne_self {l : Literal} : l.neg ≠ l := by
  cases l
  simp_all [neg]

theorem eq_neg_of_var_eq { l l' : Literal }
  (hv : l.var = l'.var) (h_neq : l ≠ l') :
  l = l'.neg := by
  obtain ⟨v, p⟩ := l
  obtain ⟨v', p'⟩ := l'
  simp_all [neg]
  cases p <;> cases p' <;> simp_all

def eval (ω : Assignment) (l : Literal) : Bool :=
  if l.pos
  then ω l.var
  else !ω l.var

@[simp]
theorem eval_ofVar {ω : Assignment} {v : Variable} :
  (ofVar v).eval ω = ω v := by
  simp [eval, ofVar]

@[simp]
theorem eval_neg {ω : Assignment} {l : Literal} :
  l.neg.eval ω = !l.eval ω := by
  obtain ⟨v, p⟩ := l
  cases p <;> simp [eval]

theorem eval_or_eval_neg {ω : Assignment} {l : Literal} :
  l.eval ω ∨ l.neg.eval ω := by
  cases h : l.eval ω <;> simp [h]

end Literal

abbrev Clause := Finset Literal

namespace Clause

def Sat (ω : Assignment) (c : Clause) : Prop :=
  ∃ l ∈ c, l.eval ω

instance (ω : Assignment) (c : Clause) : Decidable (Sat ω c) :=
  inferInstanceAs (Decidable (∃ l ∈ c, l.eval ω))

@[simp]
theorem not_sat_empty {ω : Assignment} :
  ¬ Sat ω ∅ := by
  simp [Sat]

@[simp]
theorem sat_singleton {ω : Assignment} {l : Literal} :
  Sat ω {l} ↔ l.eval ω := by
  simp [Sat]

theorem sat_union {ω : Assignment} {c c' : Clause} :
  Sat ω (c ∪ c') ↔ Sat ω c ∨ Sat ω c' := by
  simp [Sat, or_and_right, exists_or]

theorem Sat.mono {ω : Assignment} {c c' : Clause} (h : c ⊆ c') (hc : Sat ω c) :
  Sat ω c' := by
  unfold Sat at *
  obtain ⟨l, hl, h_l_eval⟩ := hc
  exact ⟨l, h hl, h_l_eval⟩

end Clause

abbrev CNF := Finset Clause

namespace CNF

def Sat (ω : Assignment) (Φ : CNF) : Prop :=
  ∀ {c}, c ∈ Φ → c.Sat ω

instance (ω : Assignment) (Φ : CNF) : Decidable (Sat ω Φ) :=
  inferInstanceAs (Decidable (∀ {c}, c ∈ Φ → c.Sat ω))

def Satisfiable (Φ : CNF) : Prop :=
  ∃ ω, Sat ω Φ

def Unsatisfiable (Φ : CNF) : Prop :=
  ¬ Satisfiable Φ

@[simp]
theorem sat_empty {ω : Assignment} :
  Sat ω ∅ := by
  simp [Sat]

@[simp]
theorem sat_singleton {ω : Assignment} {c : Clause} :
  CNF.Sat ω {c} ↔ c.Sat ω := by
  simp [CNF.Sat]

@[simp]
theorem sat_insert {ω : Assignment} {c : Clause} {Φ : CNF} :
  Sat ω (insert c Φ) ↔ c.Sat ω ∧ Φ.Sat ω := by
  simp [Sat]

theorem sat_union {ω : Assignment} {Φ Ψ : CNF} :
  Sat ω (Φ ∪ Ψ) ↔ Sat ω Φ ∧ Sat ω Ψ := by
  simp [Sat, or_imp, forall_and]

theorem not_sat_of_empty_mem {ω : Assignment} {Φ : CNF} (h : ∅ ∈ Φ) :
  ¬ Sat ω Φ := by
  intro hs
  exact Clause.not_sat_empty (hs h)

theorem unsat_iff {Φ : CNF} : Unsatisfiable Φ ↔ ∀ {ω}, ¬ Sat ω Φ := by
  simp [Unsatisfiable, Satisfiable]

theorem unsat_of_empty_mem {Φ : CNF} (h : ∅ ∈ Φ) :
  Unsatisfiable Φ := by
  rw [unsat_iff]
  intro ω
  exact not_sat_of_empty_mem h

theorem Sat.mono {ω : Assignment} {Φ Ψ : CNF} (h : Φ ⊆ Ψ) (hΨ : Sat ω Ψ) :
  Sat ω Φ := by
  intro c hc
  exact hΨ (h hc)

theorem Satisfiable.mono {Φ Ψ : CNF} (h : Φ ⊆ Ψ) (hΨ : Satisfiable Ψ) :
  Satisfiable Φ := by
  unfold Satisfiable at *
  obtain ⟨ω, hω⟩ := hΨ
  exact ⟨ω, Sat.mono h hω⟩

theorem Unsatisfiable.mono {Φ Ψ : CNF} (h : Φ ⊆ Ψ) (hΦ : Unsatisfiable Φ) :
  Unsatisfiable Ψ := by
  unfold Unsatisfiable Satisfiable at *
  intro ⟨ω, hω⟩
  exact hΦ ⟨ω, Sat.mono h hω⟩

end CNF

end LeanZKCEC
