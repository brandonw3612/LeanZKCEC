import LeanZKCEC.Logic.Basic

namespace LeanZKCEC

def ResolutionStep (c c' r : Clause) : Prop :=
  ∃ p : Literal, c ⊆ insert p r ∧ c' ⊆ insert p.neg r

def resolve (c c' : Clause) (p : Literal) : Clause :=
  (c.erase p) ∪ (c'.erase p.neg)

theorem resolutionStep_resolve {c c' : Clause} {p : Literal} :
  ResolutionStep c c' (resolve c c' p) := by
  unfold ResolutionStep
  refine ⟨p, ?_, ?_⟩ <;> intro l hl
  · by_cases h : l = p <;> simp_all [resolve]
  · by_cases h : l = p.neg <;> simp_all [resolve]

theorem ResolutionStep.sound {c c' r : Clause} {ω : Assignment}
  (hr : ResolutionStep c c' r) (h : c.Sat ω) (h' : c'.Sat ω) :
  r.Sat ω := by
  unfold Clause.Sat ResolutionStep at *
  obtain ⟨p, hc, hc'⟩ := hr
  rcases p.eval_or_eval_neg (ω := ω) with hp | hp
  · obtain ⟨l, hl, hv⟩ := h'
    have hl := hc' hl
    simp at hl
    rcases hl with rfl | hl
    · simp_all
    · exact ⟨l, hl, hv⟩
  · obtain ⟨l, hl, hv⟩ := h
    have hl := hc hl
    simp at hl
    rcases hl with rfl | hl
    · simp_all
    · exact ⟨l, hl, hv⟩

inductive Derivable (Φ : CNF) : Clause → Prop
  | input {c : Clause} : c ∈ Φ → Derivable Φ c
  | resolution {c c' r : Clause} :
    Derivable Φ c → Derivable Φ c' → ResolutionStep c c' r → Derivable Φ r

theorem Derivable.sound {Φ : CNF} {c : Clause} {ω : Assignment}
  (h : Derivable Φ c) (h_sat : Φ.Sat ω) :
  c.Sat ω := by
  induction h with
  | input hc => next c => exact h_sat hc
  | resolution h_c_der h_c'_der hr ih_c ih_c' => exact hr.sound ih_c ih_c'

theorem Derivable.unsat {Φ : CNF} (h : Derivable Φ ∅) :
  Φ.Unsatisfiable := by
  rw [CNF.unsat_iff]
  intro ω hω
  exact Clause.not_sat_empty (h.sound hω)

theorem Derivable.mono {Φ Ψ : CNF} {c : Clause}
  (h : Derivable Φ c) (h_sub : Φ ⊆ Ψ) :
  Derivable Ψ c := by
  induction h with
  | input hc => exact Derivable.input (h_sub hc)
  | resolution h_c_der h_c'_der hr ih_c ih_c' => exact Derivable.resolution ih_c ih_c' hr

structure Step where
  left : ℕ
  right : ℕ
  resolvent : Clause

def StepValid (known : List Clause) (s : Step) : Prop :=
  ∃ c c', known[s.left]? = some c ∧ known[s.right]? = some c' ∧
          ResolutionStep c c' s.resolvent

def ValidFrom : List Clause → List Step → Prop
  | _, [] => True
  | known, s :: ss => StepValid known s ∧ ValidFrom (known ++ [s.resolvent]) ss

def Refutation (init : List Clause) (steps : List Step) : Prop :=
  ValidFrom init steps ∧ ∃ pre s, steps = pre ++ [s] ∧ s.resolvent = ∅

theorem mem_of_getElem?_eq_some {l : List Clause} {n : ℕ} {c : Clause}
  (h : l[n]? = some c) : c ∈ l :=
  List.mem_iff_getElem?.2 ⟨n, h⟩

theorem ValidFrom.derivable {Φ : CNF} {steps : List Step} :
  ∀ {known : List Clause}, ValidFrom known steps → (∀ {c}, c ∈ known → Derivable Φ c) →
    ∀ {s}, s ∈ steps → Derivable Φ s.resolvent := by
  induction steps with intro known h_vf h_der s' hs'
  | nil =>
    simp at hs'
  | cons s ss ih =>
    unfold ValidFrom StepValid at h_vf
    obtain ⟨⟨c, c', hc, hc', r⟩, h_vf_kr⟩ := h_vf
    let h_c_der : Derivable Φ c := h_der (mem_of_getElem?_eq_some hc)
    let h_c'_der : Derivable Φ c' := h_der (mem_of_getElem?_eq_some hc')
    rcases List.mem_cons.mp hs' with rfl | hs'
    · exact Derivable.resolution h_c_der h_c'_der r
    · apply ih h_vf_kr
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact h_der hc
        · rw [List.mem_singleton] at hc
          subst hc
          exact Derivable.resolution h_c_der h_c'_der r
      · exact hs'

theorem Refutation.unsat {init : List Clause} {steps : List Step}
  (h : Refutation init steps) :
  CNF.Unsatisfiable init.toFinset := by
  unfold Refutation at h
  obtain ⟨h_vf, ⟨pre, s, ⟨h_steps, h_res⟩⟩⟩ := h
  apply Derivable.unsat
  rw [← h_res]
  apply ValidFrom.derivable h_vf
  · intro c hc
    exact Derivable.input (List.mem_toFinset.2 hc)
  · simp_all

end LeanZKCEC
