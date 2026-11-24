import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2515
    (eliminate : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates ∧ PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x11 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x11))
    (theta : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 ≤ (3 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan nots first computes
  obtain ⟨i,j,order,_early,ni,nj,_⟩ := nots
  let charged := fun g : Gate => GateOp.rec
    (motive := fun _ => Bool) true true false (fun _ => true) true g.op
  let edge := fun x : Fin 9 → Bool =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
      (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  have eqEdge : circuitFun 9 C = edge := computes.trans (by decide +kernel)
  obtain ⟨gates,out⟩ := C
  cases gates with
  | nil => exact Fin.elim0 i
  | cons g gs =>
    let tail : Circuit := ⟨gs,out⟩
    let ports : List (Fin 9) := List.ofFn id ++ [2]
    let f := fun x : Fin 9 → Bool => tail.eval (ports.map x)
    let step := fun (w : List Bool) (a : Gate) =>
      w ++ [a.op.eval (a.inputs.map fun k => w.getD k false)]
    have stable (rest : List Gate) (w : List Bool) (k : ℕ) (h : k < w.length) :
        (rest.foldl step w).getD k false = w.getD k false := by
      induction rest generalizing w with
      | nil => rfl
      | cons a rest ih =>
        rw [List.foldl_cons, ih (step w a) (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ h
    have agrees (x : Fin 9 → Bool) (h : x 0 = false ∨ x 2 = true) : f x = edge x := by
      let w := List.ofFn x
      have hw : w.length = 9 := by simp [w]
      have a := first x
      change (gs.foldl step (step w g)).getD 9 false = _ at a
      rw [stable _ _ _ (by simp [step, hw])] at a
      have last : (step w g).getD 9 false = g.op.eval (g.inputs.map fun j => w.getD j false) := calc
        _ = (step w g).getD w.length false := congrArg (fun j => (step w g).getD j false) hw.symm
        _ = _ := by simp [step]
      rw [last] at a
      have orEq : (x 0 || x 2) = x 2 := by rcases h with h|h <;> simp [h]
      have start : ports.map x = step w g := by
        simp only [ports, step, List.map_append, List.map_singleton, List.map_ofFn, a, orEq]
        rfl
      change (gs.foldl step (ports.map x)).getD out false = edge x
      rw [start]
      exact congrFun eqEdge x
    let i0 : Fin 9 := 0
    let i4 : Fin 8 := 3
    let f8 := fun x : Fin 8 → Bool => edge (i0.insertNth false x)
    have restrict0 (x : Fin 8 → Bool) : f (i0.insertNth false x) = f8 x :=
      agrees _ (.inl (Fin.insertNth_apply_same ..))
    have tailFan : FanInTwo tail := fun t ht => fan t (List.mem_cons_of_mem g ht)
    have dep0 : ∃ x, f (Function.update x i0 true) ≠ f (Function.update x i0 false) := by
      refine ⟨fun q => decide (q = 2 ∨ q = 4), ?_⟩
      rw [agrees _ (.inr (by decide)), agrees _ (.inr (by decide))]
      decide
    have nc8 : ∃ y z, f (i0.insertNth false y) ≠ f (i0.insertNth false z) := by
      refine ⟨fun _ => true, fun _ => false, ?_⟩
      rw [restrict0, restrict0]
      decide
    obtain ⟨D, fanD, c1, eqD⟩ := eliminate 8 i0 tail ports tailFan dep0 nc8
    have Dval (x : Fin 8 → Bool) : D.eval ((List.ofFn (id : Fin 8 → Fin 8)).map x) = f8 x := by
      rw [List.map_ofFn]
      exact (congrFun eqD x).trans (restrict0 x)
    have dep4 : ∃ x : Fin 8 → Bool,
        f8 (Function.update x i4 true) ≠ f8 (Function.update x i4 false) := by
      exact ⟨fun q => decide (q = 2), by decide⟩
    have nc7 : ∃ y z, f8 (i4.insertNth false y) ≠ f8 (i4.insertNth false z) := by
      exact ⟨fun _ => true, fun _ => false, by decide⟩
    obtain ⟨T, fanT, c2, eqT⟩ := eliminate 7 i4 D (List.ofFn id) fanD
      (by simpa only [Dval] using dep4) (by simpa only [Dval] using nc7)
    have small := theta T fanT (eqT.trans (by
      funext y
      dsimp only
      rw [Dval]
      exact (by decide +kernel : ∀ z : Fin 7 → Bool, f8 (i4.insertNth false z) =
        ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] :
          List (Fin 7 × Fin 7)).any fun e => z e.1 && z e.2) y))
    have positive : 0 < i.val := by
      by_contra! notPositive
      have indexZero : i.val = 0 := by omega
      have gateNot : g.op = .not := by
        simpa [List.get_eq_getElem, indexZero] using ni
      let zeroRow : Fin 9 → Bool := fun _ => false
      let initial := List.ofFn zeroRow
      have initialLength : initial.length = 9 := List.length_ofFn
      have zeroRead (index : ℕ) : initial.getD index false = false := by
        change (List.replicate 9 false).getD index false = false
        rw [List.getD_eq_getElem?_getD]
        exact List.getElem?_getD_replicate_default_eq false 9 index
      have headFalse : (g.inputs.map (fun index => initial.getD index false)).headD false = false := by
        cases g.inputs with
        | nil => rfl
        | cons firstWire _ => exact zeroRead firstWire
      have gateValue : g.op.eval (g.inputs.map (fun index => initial.getD index false)) = true := by
        rw [gateNot]
        change !(g.inputs.map (fun index => initial.getD index false)).headD false = true
        rw [headFalse]
        rfl
      have firstZero := first zeroRow
      change (gs.foldl step (step initial g)).getD 9 false = false at firstZero
      rw [stable _ _ _ (by simp [step, initialLength])] at firstZero
      rw [← initialLength] at firstZero
      have newest : (step initial g).getD initial.length false =
          g.op.eval (g.inputs.map (fun index => initial.getD index false)) := by simp [step]
      rw [newest, gateValue] at firstZero
      contradiction
    have ilt : i.val < gs.length + 1 := i.isLt
    have jlt : j.val < gs.length + 1 := j.isLt
    have lt : i.val < j.val := order
    let u : Fin gs.length := ⟨i.val-1, by omega⟩
    let v : Fin gs.length := ⟨j.val-1, by omega⟩
    have shift (a : Fin (g :: gs).length) (z : Fin gs.length) (hz : a.val = z.val + 1) :
        (g :: gs).get a = gs.get z := by simp [List.get_eq_getElem, hz]
    have hu : gs[u.val].op = .not := by
      change (gs.get u).op = .not
      rwa [← shift i u (by dsimp [u]; omega)]
    have hv : gs[v.val].op = .not := by
      change (gs.get v).op = .not
      rwa [← shift j v (by dsimp [v]; omega)]
    have neq : u.val ≠ v.val := by dsimp [u,v]; omega
    let gate : Gate := ⟨.and, []⟩
    let updated := gs.set u.val gate
    have index : v.val < updated.length := by simp [updated]
    have preserve : updated[v.val].op = .not := by
      rw [show updated[v.val] = gs[v.val] from List.getElem_set_ne neq index]
      exact hv
    have count1 : updated.countP charged = gs.countP charged + 1 := by
      simp [updated, gate, List.countP_set u.isLt, charged, hu]
    have count2 : (updated.set v.val gate).countP charged = updated.countP charged + 1 := by
      simp [gate, List.countP_set index, charged, preserve]
    have count := List.countP_le_length (p := charged) (l := updated.set v.val gate)
    simp only [List.length_set] at count
    change D.gates.countP charged + 1 ≤ gs.countP charged at c1
    change T.gates.countP charged + 1 ≤ D.gates.countP charged at c2
    change 11 ≤ T.gates.countP charged at small
    have len : updated.length = gs.length := List.length_set
    change 16 ≤ gs.length + 1
    omega
