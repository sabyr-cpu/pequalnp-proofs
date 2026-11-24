import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_prefix_getD (gs : List Gate) (x : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < x.length + j) :
    (run (gs.take j) x).getD i false = (run gs x).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_getD _ _ _ (by rw [run_length, List.length_take]; omega)).symm

lemma gate_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs x).getD i false) := by
  rw [run_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_prefix_getD gs x j i hj.le (hr i hi)

-- Compaction: dropping the gates that are not kept, renumbering the wires.

def cnt (keep : ℕ → Bool) (j : ℕ) : ℕ := ((List.range j).filter keep).length

lemma cnt_zero (keep : ℕ → Bool) : cnt keep 0 = 0 := by simp [cnt]

lemma cnt_succ (keep : ℕ → Bool) (j : ℕ) :
    cnt keep (j + 1) = cnt keep j + if keep j = true then 1 else 0 := by
  unfold cnt
  rw [List.range_succ, List.filter_append]
  cases h : keep j <;> simp [h]

lemma cnt_mono (keep : ℕ → Bool) {a b : ℕ} (h : a ≤ b) : cnt keep a ≤ cnt keep b := by
  induction b, h using Nat.le_induction with
  | base => exact le_refl _
  | succ b _ ih => rw [cnt_succ]; omega

lemma cnt_lt (keep : ℕ → Bool) {a b : ℕ} (h : a < b) (hk : keep a = true) :
    cnt keep a < cnt keep b := by
  have h1 := cnt_succ keep a
  rw [if_pos hk] at h1
  have := cnt_mono keep (show a + 1 ≤ b by omega)
  omega

lemma cnt_add (keep : ℕ → Bool) (j : ℕ) :
    cnt keep j + ((Finset.range j).filter (fun k => keep k = false)).card = j := by
  induction j with
  | zero => simp [cnt]
  | succ j ih =>
    rw [cnt_succ, Finset.range_add_one, Finset.filter_insert]
    cases h : keep j
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      simp only [Bool.false_eq_true, if_false]
      omega
    · simp only [if_true, Bool.true_eq_false, if_false]
      omega

def ren (n : ℕ) (keep : ℕ → Bool) (w : ℕ) : ℕ := if w < n then w else n + cnt keep (w - n)

def Kept (n : ℕ) (keep : ℕ → Bool) (w : ℕ) : Prop := w < n ∨ keep (w - n) = true

lemma ren_lt (n : ℕ) (keep : ℕ → Bool) (k w : ℕ) (hw : w < n + k) (hk : Kept n keep w) :
    ren n keep w < n + cnt keep k := by
  unfold ren
  split_ifs with h
  · omega
  · rcases hk with hk | hk
    · omega
    · have := cnt_lt keep (show w - n < k by omega) hk
      omega

lemma ren_self (n : ℕ) (keep : ℕ → Bool) (k : ℕ) : ren n keep (n + k) = n + cnt keep k := by
  unfold ren
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

lemma ren_small (n : ℕ) (keep : ℕ → Bool) (w : ℕ) (hw : w < n) : ren n keep w = w := by
  unfold ren
  rw [if_pos hw]

def comp (n : ℕ) (keep : ℕ → Bool) : List Gate → ℕ → List Gate
  | [], _ => []
  | g :: gs, k =>
    (if keep k = true then [⟨g.op, g.inputs.map (ren n keep)⟩] else []) ++ comp n keep gs (k + 1)

lemma comp_length (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) (k : ℕ) :
    (comp n keep gs k).length + cnt keep k = cnt keep (k + gs.length) := by
  induction gs generalizing k with
  | nil => simp [comp]
  | cons g gs ih =>
    have e : k + (g :: gs).length = k + 1 + gs.length := by simp; omega
    rw [e, ← ih (k + 1), cnt_succ]
    simp only [comp, List.length_append]
    cases h : keep k <;> simp <;> omega

lemma mem_comp (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) (k : ℕ) (g : Gate)
    (h : g ∈ comp n keep gs k) : ∃ g0 ∈ gs, g = ⟨g0.op, g0.inputs.map (ren n keep)⟩ := by
  induction gs generalizing k with
  | nil => simp [comp] at h
  | cons g1 gs ih =>
    simp only [comp, List.mem_append] at h
    rcases h with h | h
    · split_ifs at h with hk
      · simp only [List.mem_singleton] at h
        exact ⟨g1, by simp, h⟩
      · simp at h
    · obtain ⟨g0, hg0, rfl⟩ := ih (k + 1) h
      exact ⟨g0, by simp [hg0], rfl⟩

lemma comp_run (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) (k : ℕ) (W V : List Bool)
    (hW : W.length = n + k) (hV : V.length = n + cnt keep k)
    (hinv : ∀ w, w < n + k → Kept n keep w → V.getD (ren n keep w) false = W.getD w false)
    (hread : ∀ i (hi : i < gs.length), keep (k + i) = true →
      ∀ r ∈ gs[i].inputs, r < n + k + i ∧ Kept n keep r) :
    ∀ w, w < n + k + gs.length → Kept n keep w →
      (run (comp n keep gs k) V).getD (ren n keep w) false = (run gs W).getD w false := by
  induction gs generalizing k W V with
  | nil =>
    intro w hw hk
    exact hinv w (by simpa using hw) hk
  | cons g gs ih =>
    intro w hw hk
    have hread' : ∀ i (hi : i < gs.length), keep (k + 1 + i) = true →
        ∀ r ∈ gs[i].inputs, r < n + (k + 1) + i ∧ Kept n keep r := by
      intro i hi hk2 r hr
      have := hread (i + 1) (by simp; omega) (by rw [show k + (i + 1) = k + 1 + i by omega]; exact hk2)
        r (by simpa using hr)
      exact ⟨by omega, this.2⟩
    have hw' : w < n + (k + 1) + gs.length := by simp at hw; omega
    rw [run_cons]
    simp only [comp]
    rw [run_append]
    by_cases hkeep : keep k = true
    · rw [if_pos hkeep]
      have e1 : run [(⟨g.op, g.inputs.map (ren n keep)⟩ : Gate)] V =
          step V ⟨g.op, g.inputs.map (ren n keep)⟩ := rfl
      rw [e1]
      have hW1 : (step W g).length = n + (k + 1) := by rw [step_length]; omega
      have hV1 : (step V ⟨g.op, g.inputs.map (ren n keep)⟩).length = n + cnt keep (k + 1) := by
        rw [step_length, cnt_succ, if_pos hkeep]; omega
      have hinv1 : ∀ u, u < n + (k + 1) → Kept n keep u →
          (step V ⟨g.op, g.inputs.map (ren n keep)⟩).getD (ren n keep u) false =
            (step W g).getD u false := by
        intro u hu hku
        by_cases hlt : u < n + k
        · rw [step_getD _ _ _ (by rw [hV]; exact ren_lt n keep k u hlt hku),
            step_getD _ _ _ (by omega)]
          exact hinv u hlt hku
        · have hu' : u = n + k := by omega
          subst hu'
          rw [ren_self, ← hV, step_getD_last, ← hW, step_getD_last]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro r hr
          have := hread 0 (by simp) (by simpa using hkeep) r (by simpa using hr)
          simp only [Function.comp]
          exact hinv r (by simpa using this.1) this.2
      exact ih (k + 1) (step W g) _ hW1 hV1 hinv1 hread' w hw' hk
    · rw [if_neg hkeep, run_nil]
      have hW1 : (step W g).length = n + (k + 1) := by rw [step_length]; omega
      have hV1 : V.length = n + cnt keep (k + 1) := by
        rw [cnt_succ, if_neg hkeep]; omega
      have hinv1 : ∀ u, u < n + (k + 1) → Kept n keep u →
          V.getD (ren n keep u) false = (step W g).getD u false := by
        intro u hu hku
        by_cases hlt : u < n + k
        · rw [step_getD _ _ _ (by omega)]
          exact hinv u hlt hku
        · exfalso
          have hu' : u = n + k := by omega
          subst hu'
          rcases hku with h | h
          · omega
          · rw [Nat.add_sub_cancel_left] at h
            exact hkeep h
      exact ih (k + 1) (step W g) V hW1 hV1 hinv1 hread' w hw' hk

-- Reading back, as a list predicate.

def RB : ℕ → List Gate → Prop
  | _, [] => True
  | s, g :: gs => (∀ i ∈ g.inputs, i < s) ∧ RB (s + 1) gs

lemma RB_append (s : ℕ) (l1 l2 : List Gate) :
    RB s (l1 ++ l2) ↔ RB s l1 ∧ RB (s + l1.length) l2 := by
  induction l1 generalizing s with
  | nil => simp [RB]
  | cons g l ih =>
    simp only [List.cons_append, RB, ih, List.length_cons]
    rw [show s + 1 + l.length = s + (l.length + 1) by omega]
    tauto

lemma RB_get (s : ℕ) (gs : List Gate) (h : RB s gs) (j : ℕ) (hj : j < gs.length) :
    ∀ i ∈ gs[j].inputs, i < s + j := by
  induction gs generalizing s j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simpa using h.1
    | succ j =>
      intro i hi
      have := ih (s + 1) h.2 j (by simpa using hj) i (by simpa using hi)
      omega

lemma comp_RB (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) (k : ℕ)
    (hread : ∀ i (hi : i < gs.length), keep (k + i) = true →
      ∀ r ∈ gs[i].inputs, r < n + k + i ∧ Kept n keep r) :
    RB (n + cnt keep k) (comp n keep gs k) := by
  induction gs generalizing k with
  | nil => simp [comp, RB]
  | cons g gs ih =>
    simp only [comp]
    rw [RB_append]
    have ih' := ih (k + 1) (fun i hi hk r hr => by
      have := hread (i + 1) (by simp; omega)
        (by rw [show k + (i + 1) = k + 1 + i by omega]; exact hk) r (by simpa using hr)
      exact ⟨by omega, this.2⟩)
    by_cases hkeep : keep k = true
    · rw [if_pos hkeep]
      have e : n + cnt keep (k + 1) = n + cnt keep k + 1 := by
        rw [cnt_succ, if_pos hkeep]; omega
      rw [e] at ih'
      refine ⟨⟨?_, trivial⟩, by simpa using ih'⟩
      intro i hi
      simp only [List.mem_map] at hi
      obtain ⟨r, hr, rfl⟩ := hi
      have := hread 0 (by simp) (by simpa using hkeep) r (by simpa using hr)
      exact ren_lt n keep k r (by simpa using this.1) this.2
    · rw [if_neg hkeep]
      have e : n + cnt keep (k + 1) = n + cnt keep k := by
        rw [cnt_succ, if_neg hkeep]; omega
      rw [e] at ih'
      exact ⟨trivial, by simpa using ih'⟩

-- An OR chain.

def chain : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | q, l :: ls, p => ⟨GateOp.or, [q, l]⟩ :: chain p ls (p + 1)

def chainOut : ℕ → List ℕ → ℕ → ℕ
  | q, [], _ => q
  | _, _ :: ls, p => chainOut p ls (p + 1)

lemma chain_length (ls : List ℕ) (q p : ℕ) : (chain q ls p).length = ls.length := by
  induction ls generalizing q p with
  | nil => rfl
  | cons l ls ih => simp [chain, ih]

lemma chain_ops (ls : List ℕ) (q p : ℕ) (g : Gate) (hg : g ∈ chain q ls p) :
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction ls generalizing q p with
  | nil => simp [chain] at hg
  | cons l ls ih =>
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih p (p + 1) hg

lemma chain_RB (ls : List ℕ) (q p : ℕ) (hq : q < p) (hl : ∀ l ∈ ls, l < p) :
    RB p (chain q ls p) := by
  induction ls generalizing q p with
  | nil => simp [chain, RB]
  | cons l ls ih =>
    simp only [chain, RB]
    refine ⟨?_, ih p (p + 1) (by omega) (fun l' hl' => by
      have := hl l' (by simp [hl']); omega)⟩
    intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    · exact hq
    · exact hl _ (by simp)

lemma chain_run (ls : List ℕ) (q p : ℕ) (W : List Bool) (hW : W.length = p) (hq : q < p)
    (hl : ∀ l ∈ ls, l < p) :
    (run (chain q ls p) W).getD (chainOut q ls p) false = true ↔
      (W.getD q false = true ∨ ∃ l ∈ ls, W.getD l false = true) := by
  induction ls generalizing q p W with
  | nil => simp [chain, chainOut, run]
  | cons l ls ih =>
    simp only [chain, chainOut, run_cons]
    rw [ih p (p + 1) _ (by rw [step_length, hW]) (by omega)
      (fun l' hl' => by have := hl l' (by simp [hl']); omega)]
    have e1 : (step W ⟨GateOp.or, [q, l]⟩).getD p false = (W.getD q false || W.getD l false) := by
      rw [← hW, step_getD_last]
      simp [GateOp.eval]
    have e2 : ∀ l' ∈ ls, (step W ⟨GateOp.or, [q, l]⟩).getD l' false = W.getD l' false :=
      fun l' hl' => step_getD _ _ _ (by rw [hW]; exact hl l' (by simp [hl']))
    have e3 : (∃ l' ∈ ls, (step W ⟨GateOp.or, [q, l]⟩).getD l' false = true) ↔
        ∃ l' ∈ ls, W.getD l' false = true := by
      constructor
      · rintro ⟨l', hl', h⟩
        exact ⟨l', hl', by rw [e2 l' hl'] at h; exact h⟩
      · rintro ⟨l', hl', h⟩
        exact ⟨l', hl', by rw [e2 l' hl']; exact h⟩
    rw [e1, e3]
    simp only [Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    tauto

-- The OR tree on top of the circuit.

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma gateAt_out (C : Circuit) (j : ℕ) (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  exact List.getD_eq_default _ _ hj

lemma cval_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (run C.gates x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  rw [gateAt_eq C j hj]
  have := gate_val C.gates x j hj (by
    intro i hi
    have := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
    omega)
  rw [hx] at this
  exact this

lemma tree_len (n : ℕ) (C : Circuit) (T L : Finset ℕ) (ρ : ℕ) (ht : IsOrTree n C T L ρ)
    (j : ℕ) (hj : j ∈ T) : j < C.gates.length := by
  by_contra h
  push_neg at h
  have := (ht.1 j hj).2.1
  rw [gateAt_out C j h] at this
  simp at this

lemma tree_down (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (T L : Finset ℕ) (ρ : ℕ) (ht : IsOrTree n C T L ρ) :
    ∀ j, j ∈ T → (run C.gates x).getD (n + j) false = true →
      ∃ l ∈ L, (run C.gates x).getD l false = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hv
    obtain ⟨hop, _, hin⟩ := ht.1 j hj
    have hjl := tree_len n C T L ρ ht j hj
    rw [cval_gate n C x hx hRB j hjl, hop] at hv
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv
    obtain ⟨i, hi, hb⟩ := hv
    rcases hin i hi with hiL | ⟨hni, hiT⟩
    · exact ⟨i, hiL, hb⟩
    · have hlt := hRB j hjl i hi
      exact ih (i - n) (by omega) hiT (by rw [show n + (i - n) = i by omega]; exact hb)

lemma reader_of (C : Circuit) (T : Finset ℕ) (w : ℕ) (h : readsIn C T w = 1) :
    ∃ t ∈ T, w ∈ (gateAt C t).inputs := by
  by_contra hc
  push_neg at hc
  have : readsIn C T w = 0 := by
    unfold readsIn
    apply Finset.sum_eq_zero
    intro t ht
    exact List.count_eq_zero_of_not_mem (hc t ht)
  omega

lemma or_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (T L : Finset ℕ) (ρ : ℕ) (ht : IsOrTree n C T L ρ) (t : ℕ) (htT : t ∈ T) (w : ℕ)
    (hw : w ∈ (gateAt C t).inputs) (hv : (run C.gates x).getD w false = true) :
    (run C.gates x).getD (n + t) false = true := by
  have htl := tree_len n C T L ρ ht t htT
  rw [cval_gate n C x hx hRB t htl, (ht.1 t htT).1]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨w, hw, hv⟩

lemma tree_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (T L : Finset ℕ) (ρ : ℕ) (ht : IsOrTree n C T L ρ) :
    ∀ d t, C.gates.length - t = d → t ∈ T → (run C.gates x).getD (n + t) false = true →
      (run C.gates x).getD ρ false = true := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro t hd htT hv
    by_cases hρ : n + t = ρ
    · rw [← hρ]; exact hv
    · have hr := ht.2.2.1 t htT
      rw [if_neg hρ] at hr
      obtain ⟨t', ht'T, hin⟩ := reader_of C T (n + t) hr
      have ht'l := tree_len n C T L ρ ht t' ht'T
      have hlt := hRB t' ht'l (n + t) hin
      have htl := tree_len n C T L ρ ht t htT
      exact ih (C.gates.length - t') (by omega) t' rfl ht'T
        (or_up n C x hx hRB T L ρ ht t' ht'T (n + t) hin hv)

lemma tree_iff (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (T L : Finset ℕ) (r : ℕ) (hr : r ∈ T) (ht : IsOrTree n C T L (n + r)) :
    (run C.gates x).getD (n + r) false = true ↔ ∃ l ∈ L, (run C.gates x).getD l false = true := by
  constructor
  · exact tree_down n C x hx hRB T L (n + r) ht r hr
  · rintro ⟨l, hl, hv⟩
    obtain ⟨hnot, hreads⟩ := ht.2.1 l hl
    have hlρ : l ≠ n + r := by
      rintro rfl
      exact hnot ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hr⟩
    rw [if_neg hlρ] at hreads
    obtain ⟨t, htT, hin⟩ := reader_of C T l hreads
    exact tree_up n C x hx hRB T L (n + r) ht _ t rfl htT
      (or_up n C x hx hRB T L (n + r) ht t htT l hin hv)

lemma sum_count_le (l : List ℕ) (W : Finset ℕ) : ∑ w ∈ W, l.count w ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib]
    have : ∑ w ∈ W, (if (a == w) = true then 1 else 0) ≤ 1 := by
      simp only [beq_iff_eq]
      rw [Finset.sum_ite_eq]
      split_ifs <;> simp
    omega

lemma tree_count (n : ℕ) (C : Circuit) (T L : Finset ℕ) (r : ℕ) (hr : r ∈ T)
    (ht : IsOrTree n C T L (n + r)) : L.card ≤ T.card + 1 := by
  have hdisj : Disjoint L (T.image fun j => n + j) := by
    rw [Finset.disjoint_left]
    intro w hwL hwT
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hwT
    exact (ht.2.1 _ hwL).1 ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hj⟩
  have hsum : ∑ w ∈ L ∪ T.image (fun j => n + j), readsIn C T w ≤ 2 * T.card := by
    unfold readsIn
    rw [Finset.sum_comm]
    calc ∑ t ∈ T, ∑ w ∈ L ∪ T.image (fun j => n + j), (gateAt C t).inputs.count w
        ≤ ∑ t ∈ T, (gateAt C t).inputs.length :=
          Finset.sum_le_sum fun t _ => sum_count_le _ _
      _ = ∑ t ∈ T, 2 := Finset.sum_congr rfl fun t ht' => (ht.1 t ht').2.1
      _ = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [Finset.sum_union hdisj] at hsum
  have hL : ∑ w ∈ L, readsIn C T w = L.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hnot, hreads⟩ := ht.2.1 w hw
    have : w ≠ n + r := by
      rintro rfl
      exact hnot ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hr⟩
    rw [hreads, if_neg this]
  have hT : T.card - 1 ≤ ∑ w ∈ T.image (fun j => n + j), readsIn C T w := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
    calc T.card - 1 = (T.erase r).card := (Finset.card_erase_of_mem hr).symm
      _ = ∑ j ∈ T.erase r, readsIn C T (n + j) := by
          rw [Finset.card_eq_sum_ones]
          apply Finset.sum_congr rfl
          intro j hj
          rw [ht.2.2.1 j (Finset.mem_of_mem_erase hj), if_neg]
          intro h
          exact Finset.ne_of_mem_erase hj (by omega)
      _ ≤ ∑ j ∈ T, readsIn C T (n + j) :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset r T)
  have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨r, hr⟩
  omega

-- The main argument.

lemma main (n : ℕ) (C : Circuit) (T L : Finset ℕ) (i₁ i₂ a b c : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hRB : ReadsBack n C) (htree : IsOrTree n C T L C.output)
    (hL1 : n + i₁ ∈ L) (hL2 : n + i₂ ∈ L) (hne : i₁ ≠ i₂)
    (hop1 : (gateAt C i₁).op = GateOp.and)
    (hin1 : (gateAt C i₁).inputs = [a, b] ∨ (gateAt C i₁).inputs = [b, a])
    (hop2 : (gateAt C i₂).op = GateOp.and)
    (hin2 : (gateAt C i₂).inputs = [a, c] ∨ (gateAt C i₂).inputs = [c, a])
    (hout : ∀ k < C.gates.length, k ∉ T → n + i₁ ∉ (gateAt C k).inputs ∧
      n + i₂ ∉ (gateAt C k).inputs ∧ ∀ j ∈ T, n + j ∉ (gateAt C k).inputs) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
      D.size + 1 ≤ C.size := by
  obtain ⟨hAnd, _, hTwo⟩ := hAO
  -- the root
  have hTne : T ≠ ∅ := by
    intro hT
    have := htree.2.2.2
    rw [if_pos hT] at this
    rw [this] at hL1 hL2
    simp only [Finset.mem_singleton] at hL1 hL2
    omega
  have hroot := htree.2.2.2
  rw [if_neg hTne] at hroot
  obtain ⟨r, hrT, hρ⟩ := hroot
  rw [hρ] at htree
  -- the two AND gates
  have hi1T : i₁ ∉ T := fun h =>
    (htree.2.1 _ hL1).1 ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact h⟩
  have hi2T : i₂ ∉ T := fun h =>
    (htree.2.1 _ hL2).1 ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact h⟩
  have hi1l : i₁ < C.gates.length := by
    by_contra h
    push_neg at h
    rw [gateAt_out C i₁ h] at hop1
    cases hop1
  have hi2l : i₂ < C.gates.length := by
    by_contra h
    push_neg at h
    rw [gateAt_out C i₂ h] at hop2
    cases hop2
  -- what is kept
  let keep : ℕ → Bool := fun k => decide (k ∉ T ∧ k ≠ i₁ ∧ k ≠ i₂)
  have hreadOut : ∀ k < C.gates.length, k ∉ T → ∀ w ∈ (gateAt C k).inputs,
      w < n + k ∧ Kept n keep w := by
    intro k hk hkT w hw
    have hlt := hRB k hk w hw
    refine ⟨hlt, ?_⟩
    by_cases hwn : w < n
    · exact Or.inl hwn
    · right
      obtain ⟨h1, h2, h3⟩ := hout k hk hkT
      simp only [keep, decide_eq_true_eq]
      refine ⟨fun h => h3 _ h (by rw [show n + (w - n) = w by omega]; exact hw), ?_, ?_⟩
      · intro h; apply h1; rw [show n + i₁ = w by omega]; exact hw
      · intro h; apply h2; rw [show n + i₂ = w by omega]; exact hw
  have hread : ∀ i (hi : i < C.gates.length), keep (0 + i) = true →
      ∀ w ∈ C.gates[i].inputs, w < n + 0 + i ∧ Kept n keep w := by
    intro i hi hk w hw
    simp only [keep, Nat.zero_add, decide_eq_true_eq] at hk
    have := hreadOut i hi hk.1 w (by rw [gateAt_eq C i hi]; exact hw)
    exact ⟨by omega, this.2⟩
  -- the leaves that stay
  let ls0 : List ℕ := ((L.erase (n + i₁)).erase (n + i₂)).toList
  have hmem0 : ∀ l, l ∈ ls0 ↔ l ≠ n + i₂ ∧ l ≠ n + i₁ ∧ l ∈ L := by
    intro l
    simp only [ls0, Finset.mem_toList, Finset.mem_erase]
  have hleaf : ∀ l ∈ L, l < n + C.gates.length := by
    intro l hl
    obtain ⟨hnot, hreads⟩ := htree.2.1 l hl
    have : l ≠ n + r := by
      rintro rfl
      exact hnot ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hrT⟩
    rw [if_neg this] at hreads
    obtain ⟨t, htT, hin⟩ := reader_of C T l hreads
    have htl := tree_len n C T L (n + r) htree t htT
    have := hRB t htl l hin
    omega
  have hkept0 : ∀ l ∈ ls0, Kept n keep l := by
    intro l hl
    rw [hmem0] at hl
    obtain ⟨hl2, hl1, hlL⟩ := hl
    by_cases hln : l < n
    · exact Or.inl hln
    · right
      simp only [keep, decide_eq_true_eq]
      refine ⟨fun h => (htree.2.1 l hlL).1 ⟨by omega, h⟩, ?_, ?_⟩
      · intro h; apply hl1; omega
      · intro h; apply hl2; omega
  -- the inputs of the two AND gates
  have hab : a ∈ (gateAt C i₁).inputs ∧ b ∈ (gateAt C i₁).inputs := by
    rcases hin1 with h | h <;> rw [h] <;> simp
  have hac : a ∈ (gateAt C i₂).inputs ∧ c ∈ (gateAt C i₂).inputs := by
    rcases hin2 with h | h <;> rw [h] <;> simp
  have ha := hreadOut i₁ hi1l hi1T a hab.1
  have hb := hreadOut i₁ hi1l hi1T b hab.2
  have hc := hreadOut i₂ hi2l hi2T c hac.2
  -- the new circuit
  let P : ℕ := n + cnt keep C.gates.length
  let ls : List ℕ := ls0.map (ren n keep)
  let top : List Gate := ⟨GateOp.or, [ren n keep b, ren n keep c]⟩ ::
    ⟨GateOp.and, [ren n keep a, P]⟩ :: chain (P + 1) ls (P + 2)
  let D : Circuit := ⟨comp n keep C.gates 0 ++ top, chainOut (P + 1) ls (P + 2)⟩
  have hcl : (comp n keep C.gates 0).length = cnt keep C.gates.length := by
    have := comp_length n keep C.gates 0
    rw [cnt_zero, Nat.zero_add] at this
    omega
  have hrenb : ren n keep b < P := ren_lt n keep _ b (by omega) hb.2
  have hrenc : ren n keep c < P := ren_lt n keep _ c (by omega) hc.2
  have hrena : ren n keep a < P := ren_lt n keep _ a (by omega) ha.2
  have hrenl : ∀ l ∈ ls, l < P := by
    intro l hl
    simp only [ls, List.mem_map] at hl
    obtain ⟨l0, hl0, rfl⟩ := hl
    exact ren_lt n keep _ l0 (hleaf l0 ((hmem0 l0).mp hl0).2.2) (hkept0 l0 hl0)
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- AND and OR gates only
    intro g hg
    simp only [D, top, List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | rfl | hg
    · obtain ⟨g0, hg0, rfl⟩ := mem_comp n keep C.gates 0 g hg
      exact hAnd g0 hg0
    · right; rfl
    · left; rfl
    · right; exact (chain_ops ls (P + 1) (P + 2) g hg).1
  · -- reading back
    have hRBD : RB n D.gates := by
      simp only [D]
      rw [RB_append]
      refine ⟨by simpa [cnt_zero] using comp_RB n keep C.gates 0 hread, ?_⟩
      rw [hcl]
      simp only [top, RB]
      refine ⟨?_, ?_, chain_RB ls (P + 1) (P + 2) (by omega)
        (fun l hl => by have := hrenl l hl; omega)⟩
      · intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl
        · exact hrenb
        · exact hrenc
      · intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl
        · show ren n keep a < P + 1; omega
        · show P < P + 1; omega
    intro j hj i hi
    rw [gateAt_eq D j hj] at hi
    exact RB_get n D.gates hRBD j hj i hi
  · -- two inputs each
    intro g hg
    simp only [D, top, List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | rfl | hg
    · obtain ⟨g0, hg0, rfl⟩ := mem_comp n keep C.gates 0 g hg
      simpa using hTwo g0 hg0
    · rfl
    · rfl
    · exact (chain_ops ls (P + 1) (P + 2) g hg).2
  · -- the same function
    funext z
    let x : List Bool := List.ofFn z
    have hx : x.length = n := by simp [x]
    let Cv : ℕ → Bool := fun w => (run C.gates x).getD w false
    let V0 := run (comp n keep C.gates 0) x
    have hV0 : V0.length = P := by
      simp only [V0, run_length, hx, hcl, P]
    have hV0v : ∀ w, w < n + C.gates.length → Kept n keep w →
        V0.getD (ren n keep w) false = Cv w := by
      intro w hw hk
      have := comp_run n keep C.gates 0 x x (by simp [hx]) (by simp [hx, cnt_zero])
        (fun u hu _ => by rw [ren_small n keep u (by omega)]) hread w (by omega) hk
      exact this
    let X : Gate := ⟨GateOp.or, [ren n keep b, ren n keep c]⟩
    let Y : Gate := ⟨GateOp.and, [ren n keep a, P]⟩
    let V1 := step V0 X
    let V2 := step V1 Y
    have hV1 : V1.length = P + 1 := by simp only [V1, step_length, hV0]
    have hV2 : V2.length = P + 2 := by simp only [V2, step_length, hV1]
    have hV1P : V1.getD P false = (Cv b || Cv c) := by
      simp only [V1]
      rw [← hV0, step_getD_last]
      simp only [X, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [hV0v b (by omega) hb.2, hV0v c (by omega) hc.2]
    have hV2P : V2.getD (P + 1) false = (Cv a && (Cv b || Cv c)) := by
      simp only [V2]
      rw [← hV1, step_getD_last]
      simp only [Y, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      rw [hV1P, step_getD _ _ _ (by rw [hV0]; exact hrena), hV0v a (by omega) ha.2]
    have hV2l : ∀ l0 ∈ ls0, V2.getD (ren n keep l0) false = Cv l0 := by
      intro l0 hl0
      have hlt := ren_lt n keep _ l0 (hleaf l0 ((hmem0 l0).mp hl0).2.2) (hkept0 l0 hl0)
      simp only [V2, V1]
      rw [step_getD _ _ _ (by rw [step_length, hV0]; omega),
        step_getD _ _ _ (by rw [hV0]; exact hlt)]
      exact hV0v l0 (hleaf l0 ((hmem0 l0).mp hl0).2.2) (hkept0 l0 hl0)
    have hDrun : run D.gates x = run (chain (P + 1) ls (P + 2)) V2 := by
      simp only [D, top]
      rw [run_append]
      rfl
    have hDv : PEqualNP.MetaComplexity.circuitFun n D z = true ↔
        ((Cv a && (Cv b || Cv c)) = true ∨ ∃ l0 ∈ ls0, Cv l0 = true) := by
      change (run D.gates x).getD (chainOut (P + 1) ls (P + 2)) false = true ↔ _
      rw [hDrun, chain_run ls (P + 1) (P + 2) V2 hV2 (by omega)
        (fun l hl => by have := hrenl l hl; omega), hV2P]
      apply or_congr Iff.rfl
      simp only [ls, List.mem_map]
      constructor
      · rintro ⟨_, ⟨l0, hl0, rfl⟩, h⟩
        exact ⟨l0, hl0, by rw [← hV2l l0 hl0]; exact h⟩
      · rintro ⟨l0, hl0, h⟩
        exact ⟨_, ⟨l0, hl0, rfl⟩, by rw [hV2l l0 hl0]; exact h⟩
    have hCv : PEqualNP.MetaComplexity.circuitFun n C z = true ↔ ∃ l ∈ L, Cv l = true := by
      change (run C.gates x).getD C.output false = true ↔ _
      rw [hρ]
      exact tree_iff n C x hx hRB T L r hrT htree
    have hv1 : Cv (n + i₁) = (Cv a && Cv b) := by
      simp only [Cv]
      rw [cval_gate n C x hx hRB i₁ hi1l, hop1]
      rcases hin1 with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm]
    have hv2 : Cv (n + i₂) = (Cv a && Cv c) := by
      simp only [Cv]
      rw [cval_gate n C x hx hRB i₂ hi2l, hop2]
      rcases hin2 with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm]
    apply Bool.eq_iff_iff.mpr
    rw [hDv, hCv]
    constructor
    · rintro (h | ⟨l0, hl0, h⟩)
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨h1, h2 | h2⟩
        · exact ⟨n + i₁, hL1, by rw [hv1]; simp [h1, h2]⟩
        · exact ⟨n + i₂, hL2, by rw [hv2]; simp [h1, h2]⟩
      · exact ⟨l0, ((hmem0 l0).mp hl0).2.2, h⟩
    · rintro ⟨l, hl, h⟩
      by_cases e1 : l = n + i₁
      · left
        rw [e1, hv1] at h
        simp only [Bool.and_eq_true] at h
        simp [h.1, h.2]
      · by_cases e2 : l = n + i₂
        · left
          rw [e2, hv2] at h
          simp only [Bool.and_eq_true] at h
          simp [h.1, h.2]
        · right
          exact ⟨l, (hmem0 l).mpr ⟨e2, e1, hl⟩, h⟩
  · -- one gate fewer
    have hcard := cnt_add keep C.gates.length
    have hS : (Finset.range C.gates.length).filter (fun k => keep k = false) =
        insert i₁ (insert i₂ T) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, keep,
        decide_eq_false_iff_not, not_and, not_not]
      constructor
      · rintro ⟨_, h⟩
        by_cases hkT : k ∈ T
        · exact Or.inr (Or.inr hkT)
        · by_cases hk1 : k = i₁
          · exact Or.inl hk1
          · exact Or.inr (Or.inl (by_contra fun hk2 => absurd (h hkT hk1) hk2))
      · rintro (rfl | rfl | hkT)
        · exact ⟨hi1l, fun _ h => absurd rfl h⟩
        · exact ⟨hi2l, fun _ _ => rfl⟩
        · exact ⟨tree_len n C T L (n + r) htree k hkT, fun h => absurd hkT h⟩
    rw [hS, Finset.card_insert_of_notMem (by simp [hne, hi1T]),
      Finset.card_insert_of_notMem hi2T] at hcard
    have hTL := tree_count n C T L r hrT htree
    have hls : ls0.length = L.card - 2 := by
      simp only [ls0, Finset.length_toList]
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨by omega, hL2⟩),
        Finset.card_erase_of_mem hL1]
      omega
    have hL2c : 2 ≤ L.card := by
      have : ({n + i₁, n + i₂} : Finset ℕ) ⊆ L := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hL1
        · exact hL2
      have h2 := Finset.card_le_card this
      rw [Finset.card_pair (by omega)] at h2
      exact h2
    change (comp n keep C.gates 0 ++ top).length + 1 ≤ C.gates.length
    simp only [top, List.length_append, List.length_cons, chain_length, ls, List.length_map, hcl]
    omega

end PEqualNP.Outside.L_meta_2774

theorem PEqualNP.Outside.L_meta_2774 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (i₁ i₂ a b c : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output ∧
  n + i₁ ∈ L ∧ n + i₂ ∈ L ∧ i₁ ≠ i₂ ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [b, a]) ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [c, a]) ∧
  (∀ k < C.gates.length, k ∉ T → n + i₁ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ n + i₂ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧
    ∀ j ∈ T, n + j ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
  PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + 1 ≤ C.size := by
  intro n C T L i₁ i₂ a b c h
  obtain ⟨hAO, hRB, htree, hL1, hL2, hne, hop1, hin1, hop2, hin2, hout⟩ := h
  exact PEqualNP.Outside.L_meta_2774.main n C T L i₁ i₂ a b c hAO hRB htree hL1 hL2 hne hop1 hin1
    hop2 hin2 hout
